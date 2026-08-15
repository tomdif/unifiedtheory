#!/usr/bin/env python3
"""SHARP LAMBDA PREDICTION + MATCHED-FILTER FIT (and a CORRECTION).

CORRECTION (referee note on our own conversion, 2026-08-15): the
(1-lambda) bounds committed yesterday used the ENVELOPE
S_k = sum(|I_d| + |I_(d+1)|) with a saturation assumption.  That is
not the lambda-theory's prediction.  If observed frequencies
estimate the normalized interpolated measure

    f_(lam,d)(E) = [(1-lam) Q_d(E) + lam P_d(E)]
                   / [(1-lam) Q_d(Omega) + lam],

then to first order in (1-lam) the predicted regression of record k
between horizons k+1 and T is the SIGNED fingerprint

    delta_k^pred = (1-lam) * F_k,
    F_k = [Q_(k+1)(E_k) - P(E_k) Q_(k+1)(Omega)]
        - [Q_T(E_k)     - P(E_k) Q_T(Omega)].

This is sharper than the envelope in structure (a signed PATTERN
across records - a matched filter) but smaller in magnitude, so the
resulting bound is WEAKER than the envelope numbers we quoted; the
envelope numbers are hereby superseded.  Remaining assumption: the
growth-to-circuit mapping (computational-basis branch labels, stated
in lambda_theory_I.py).

Fit: weighted least squares of measured deltas against F_k using the
CLEAN datasets (ibm_kingston all-null; marrakesh v6 records 1-3,
record 0 excluded as the identified path-end hardware artifact).

Registered readings:
  (i)  fit consistent with 0: report (1-lam) central +- sigma and
       the 95% one-sided upper bound.
  (ii) fit nonzero > 3 sigma WITH acceptable chi2: flag for
       replication (a fingerprint detection would be extraordinary
       and is not claimable from these data alone).
"""
import json, math
import numpy as np
from qiskit import QuantumCircuit
from qiskit.quantum_info import Statevector

T = 5
THETAS = [0.9, 1.3, 0.7, 1.1, 0.5]
PHIS = [0.4, 1.0, 0.6, 1.2, 0.8]

def full_circuit_upto(d):
    qc = QuantumCircuit(T + 1)
    qc.h(0)
    for k in range(d):
        qc.ry(THETAS[k], k)
        qc.rz(PHIS[k], k)
        qc.swap(k, k + 1)
        qc.cx(k + 1, k)
    return qc

Q_E, P_E, Q_O = {}, {}, {}
for d in range(1, T + 1):
    sv = Statevector.from_instruction(full_circuit_upto(d)).data
    Q_O[d] = float(np.abs(np.sum(sv)) ** 2)
    for k in range(d):
        idx = [x for x in range(2 ** (T + 1)) if (x >> k) & 1]
        c = sv[idx]
        P_E[(k, d)] = float(np.sum(np.abs(c) ** 2))
        Q_E[(k, d)] = float(np.abs(np.sum(c)) ** 2)

print("normalizations Q_d(Omega):",
      {d: round(Q_O[d], 4) for d in Q_O})
print("\nfingerprint F_k (delta_k^pred = (1-lambda) * F_k):")
F = {}
for k in range(T - 1):
    a = Q_E[(k, k + 1)] - P_E[(k, k + 1)] * Q_O[k + 1]
    b = Q_E[(k, T)] - P_E[(k, T)] * Q_O[T]
    F[k] = a - b
    print(f"  F_{k} = {F[k]:+.4f}")

DATASETS = [
    ("ibm_kingston v7b",
     "logs_lambda_hw_v7b_ibm_kingston_2026-08-15T113049.json",
     [0, 1, 2, 3]),
    ("marrakesh v6 (rec 1-3; rec 0 excluded: hardware artifact)",
     "logs_lambda_hw_v6_ibm_marrakesh_2026-08-14T211453.json",
     [1, 2, 3]),
]

num = den = 0.0
print("\nper-dataset contributions:")
rows = []
for name, path, keep in DATASETS:
    meta = json.load(open(path))
    for row in meta["deltas"]:
        k, d_, se = row[0], row[1], row[2]
        if k not in keep or abs(F[k]) < 1e-6:
            continue
        est = d_ / F[k]
        sig = se / abs(F[k])
        rows.append((name, k, est, sig))
        w = 1.0 / sig ** 2
        num += w * est
        den += w
        print(f"  {name} record {k}: (1-lam) = {est:+.5f} ± {sig:.5f}")

lam_hat = num / den
lam_sig = 1.0 / math.sqrt(den)
chi2 = sum(((e - lam_hat) / s) ** 2 for _, _, e, s in rows)
ndof = len(rows) - 1
up95 = lam_hat + 1.645 * lam_sig

print(f"\ncombined fit: (1-lambda) = {lam_hat:+.5f} ± {lam_sig:.5f}"
      f"   chi2/dof = {chi2:.1f}/{ndof}")
print("--- VERDICT (registered readings) ---")
if abs(lam_hat) < 3 * lam_sig:
    print(f"  reading (i): consistent with lambda = 1.")
    print(f"  (1 - lambda) <= {max(up95, 0):.5f}  (95% CL, one-sided,"
          " matched-filter, mapping assumption stated)")
else:
    print(f"  reading (ii): nonzero fit ({lam_hat/lam_sig:+.1f} "
          "sigma) - NOT claimable; replication required.")
print("\nSUPERSEDES the envelope-based conversion of "
      "2026-08-14 (which assumed saturation the theory does not "
      "provide); see docstring.")
