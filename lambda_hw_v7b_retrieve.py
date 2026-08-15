#!/usr/bin/env python3
"""Retrieve + analyze the queued ibm_kingston cross-backend
discriminator (job d9vostvo3ppc73akkil0, submitted 2026-08-14,
15 pubs = 5 depths x 3 repeats, seeded shuffle 20260814).

Run this any time; exits quietly if the job is still queued.
Readings as in lambda_hw_run7.py: the record-0 excess measured
+0.0118(16) on marrakesh forward and +0.0591(25) on marrakesh
reversed - magnitude tracking the physical mapping.  Kingston:
  ABSENT or different magnitude -> hardware attribution SEALED;
  the clean-record bound stands.
  comparable magnitude to either -> iterate (angle variation)."""
import json, math, random, sys
from datetime import datetime, timezone
from qiskit_ibm_runtime import QiskitRuntimeService

JOB = "d9vostvo3ppc73akkil0"
T, R = 5, 3

svc = QiskitRuntimeService()
job = svc.job(JOB)
st = str(job.status())
print("status:", st)
if "DONE" not in st:
    sys.exit(0)

order = [(r, d) for r in range(R) for d in range(1, T + 1)]
random.Random(20260814).shuffle(order)
result = job.result()

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

print("--- pooled record probabilities (ibm_kingston) ---")
for k in range(T):
    row = "  ".join(f"d={d}: {P_pool(k,d)[0]:.4f}"
                    for d in range(k + 1, T + 1))
    print(f"  ancilla {k}: {row}")

print("--- pooled regression estimators ---")
deltas = []
for k in range(T - 1):
    p1, n1 = P_pool(k, k + 1)
    p2, n2 = P_pool(k, T)
    d_ = p1 - p2
    se = math.sqrt(p1 * (1 - p1) / n1 + p2 * (1 - p2) / n2)
    deltas.append((k, d_, se))
    print(f"  record {k}: delta = {d_:+.4f} ± {se:.4f} "
          f"({d_/se:+.1f} sigma)")

k0, d0, s0 = deltas[0]
print("--- record-0 cross-backend verdict ---")
if d0 > 3 * s0:
    print(f"  PERSISTS on kingston: {d0:+.4f} "
          f"(marrakesh fwd +0.0118, rev +0.0591) -> compare "
          "magnitudes; comparable -> iterate, different -> hardware.")
else:
    print(f"  ABSENT on kingston: {d0:+.4f} ({d0/s0:+.1f} sigma) "
          "-> hardware attribution SEALED.")

meta = {
    "utc": datetime.now(timezone.utc).isoformat(),
    "protocol": "v7b-kingston-retrieved",
    "backend": "ibm_kingston",
    "job_id": JOB,
    "counts": counts_log,
    "deltas": deltas,
}
out = f"logs_lambda_hw_v7b_ibm_kingston_{meta['utc'][:19].replace(':','')}.json"
with open(out, "w") as f:
    json.dump(meta, f, indent=1)
print("saved", out)
