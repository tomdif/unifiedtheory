#!/usr/bin/env python3
"""THEORY-SIDE INTERFERENCE MEASURES FOR THE HARDWARE CIRCUIT FAMILY
(registered follow-up of the first hardware bound, tag
lambda-hw-first-bound-2026-08-14).

Purpose: convert the measured record-regression bound
eps_RR <= eps_exp into a bound on (1 - lambda) of the bi-normalized
lambda-family, whose envelope is

    per-step regression of a monotone record E at horizon d
        <=  (1 - lambda) * (|I_d(E)| + |I_{d+1}(E)|),

I_d(E) := Q_d(E) - P_d(E), where P is the Born measure and Q the
class-coherent measure of the event.  MAPPING (stated, not derived):
the growth-framework horizon d corresponds to circuit stage d of the
FULL line-walk protocol (all records written); branch labels are the
computational basis; for an event E (a set of basis labels),
P_d(E) = sum_{x in E} |c_x|^2 and Q_d(E) = |sum_{x in E} c_x|^2
with c_x the stage-d statevector amplitudes.  E_k = {ancilla_k = 1}.

The measured total regression delta_k = P_k(k+1) - P_k(T) telescopes
over T-1-k steps, so the envelope for it is (1-lambda) * S_k with
    S_k = sum_{d=k+1}^{T-1} (|I_d(E_k)| + |I_{d+1}(E_k)|).

CONDITIONAL CONVERSION (assumption stated): if the lambda-dynamics
saturates a fraction f of its envelope on this family (simulation of
the growth engine measured tightness up to 0.83 on its native trees;
f for THIS family is not derived), then

    (1 - lambda)  <=  delta_k^{95} / (f * S_k)   for every k,

and the best (smallest) usable ratio is reported at f = 1 (envelope
saturation, the conservative-for-lambda choice), f = 0.83, f = 0.5.
Records with S_k below S_MIN = 0.02 are excluded (no leverage).

Registered readings:
  (a) at least one record has S_k >= 0.02  ->  report the
      conditional (1-lambda) bounds table; the headline number is
      min_k delta_k^{95}/S_k at f = 1.
  (b) all S_k < 0.02: this circuit family has no lambda-leverage
      (angles must be redesigned to pump interference into the
      record events); report and register the redesign.
"""
import json, math
import numpy as np
from qiskit import QuantumCircuit
from qiskit.quantum_info import Statevector

T = 5
THETAS = [0.9, 1.3, 0.7, 1.1, 0.5]
PHIS = [0.4, 1.0, 0.6, 1.2, 0.8]
S_MIN = 0.02

def full_circuit_upto(d):
    """line-walk protocol truncated after stage d (ALL records
    written along the way) - no measurements."""
    qc = QuantumCircuit(T + 1)
    qc.h(0)
    for k in range(d):
        qc.ry(THETAS[k], k)
        qc.rz(PHIS[k], k)
        qc.swap(k, k + 1)
        qc.cx(k + 1, k)
    return qc

def measures(d):
    """P_d(E_k), Q_d(E_k) for all k < d from the stage-d state."""
    sv = Statevector.from_instruction(full_circuit_upto(d)).data
    n = T + 1
    out = {}
    for k in range(d):
        amps = np.zeros(0, complex)
        idx = [x for x in range(2 ** n) if (x >> k) & 1]
        c = sv[idx]
        P = float(np.sum(np.abs(c) ** 2))
        Q = float(np.abs(np.sum(c)) ** 2)
        out[k] = (P, Q, Q - P)
    return out

M = {d: measures(d) for d in range(1, T + 1)}

print("interference table I_d(E_k) = Q_d - P_d (line-walk family):")
print("  (P_d validates against hardware marginals; Q_d is the")
print("   class-coherent measure of the same event)")
for k in range(T):
    for d in range(k + 1, T + 1):
        P, Q, I = M[d][k]
        print(f"  k={k} d={d}:  P={P:.4f}  Q={Q:.4f}  I={I:+.4f}")

print("\nenvelope sums S_k = sum_(d=k+1)^(T-1) (|I_d| + |I_(d+1)|):")
S = {}
for k in range(T - 1):
    S[k] = sum(abs(M[d][k][2]) + abs(M[d + 1][k][2])
               for d in range(k + 1, T))
    print(f"  S_{k} = {S[k]:.4f}")

# hardware numbers from the v5 (readout-matched) run
V5 = "logs_lambda_hw_v5_ibm_marrakesh_2026-08-14T210613.json"
meta = json.load(open(V5))
print(f"\ncombining with {meta['backend']} v5 deltas "
      f"(job {meta['job_id']}):")
usable = []
for k, d_, se in meta["deltas"]:
    d95 = d_ + 1.645 * se
    if S[k] >= S_MIN:
        usable.append((k, d95 / S[k]))
        print(f"  record {k}: delta95 = {d95:+.4f}, S = {S[k]:.4f}  "
              f"-> (1-lambda) <= {d95 / S[k]:.4f}  [f=1]")
    else:
        print(f"  record {k}: delta95 = {d95:+.4f}, S = {S[k]:.4f}  "
              f"-> EXCLUDED (S < {S_MIN})")

print("\n--- VERDICT (registered readings) ---")
if usable:
    k_best, b = min(usable, key=lambda t: t[1])
    print(f"  reading (a): headline conditional bound from record "
          f"{k_best}:")
    for f in (1.0, 0.83, 0.5):
        print(f"    (1 - lambda) <= {b / f:.4f}   "
              f"[envelope-saturation fraction f = {f}]")
    print("  assumption: the lambda-dynamics achieves fraction f of "
          "its envelope on this family; f is NOT derived here.")
else:
    print("  reading (b): no record has lambda-leverage on this "
          "family (all S_k < 0.02); angle redesign registered.")
