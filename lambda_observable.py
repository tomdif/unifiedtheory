#!/usr/bin/env python3
"""GATE 2: the lambda < 1 observable, quantified from the logged runs.

Theorem (KFCausalBornQuadraturePhase.fact_regression_interference_bound):
for M_lambda = (1-lambda) Q + lambda P with P the Born-diagonal
martingale channel, a monotone record's regression across a horizon
step obeys
    M_{T+1} - M_T  >=  -(1-lambda) (|I_T| + |I_{T+1}|),
I_T = Q_T - P_T the record's interference.  At lambda = 1: zero.
Standard decoherence-based QM predicts zero regression at every lambda.

This script parses the stem tables of the three logged laws
(born_records_test.log depth 7, born_records_test_d8.log depth 8,
binormalized_phase_diagram.log pi/4 action-phased law) and reports:
  (a) bound violations (must be none - implementation check of a
      theorem);
  (b) tightness: max over (stem, step) of (-Delta M)/bound when a
      regression occurs;
  (c) the observable's magnitude: per-step X_minus(Q) by depth and law
      (does the coherent regression compound with depth?);
  (d) the falsifier statement constants.
"""
import re, math

def parse_tables(path, labels):
    """labels: list of (tag, header-substring) to extract in order.
       returns {tag: {stem: [values]}}"""
    txt = open(path).read()
    out = {}
    for tag, header in labels:
        i = txt.index(header)
        block = txt[i:i + 2000]
        tab = {}
        for m in re.finditer(r"(s\d+)(?:\(n=\d\))?\s+((?:\d\.\d{4}\s*)+)",
                             block):
            vals = [float(x) for x in m.group(2).split()]
            if m.group(1) in tab: continue
            tab[m.group(1)] = vals
        assert len(tab) == 11, (path, tag, len(tab))
        out[tag] = tab
    return out

runs = []
d7 = parse_tables("born_records_test.log", [
    ("Q", "stems under Q, maxmin-completed"),
    ("P", "stems under P, maxmin-completed")])
runs.append(("maxmin-completed d7", d7))
d8 = parse_tables("born_records_test_d8.log", [
    ("Q", "stems under Q, maxmin-completed"),
    ("P", "stems under P, maxmin-completed")])
runs.append(("maxmin-completed d8", d8))
p4 = parse_tables("binormalized_phase_diagram.log", [
    ("Q", "stems under Q (pi/4"),
    ("P", "stems under P (pi/4")])
runs.append(("pi/4 action-phased d7", p4))

LAMS = [0.0, 0.25, 0.5, 0.75, 1.0]
print("law".ljust(24), "lam", "viol", "tightness", "worst regression")
falsifier_c = {}
for name, tabs in runs:
    Q, P = tabs["Q"], tabs["P"]
    stems = sorted(Q, key=lambda s: int(s[1:]))
    nT = len(Q[stems[0]])
    for lam in LAMS:
        viol = 0; tight = 0.0; worst = 0.0
        for s in stems:
            for j in range(nT - 1):
                M0 = (1 - lam) * Q[s][j] + lam * P[s][j]
                M1 = (1 - lam) * Q[s][j + 1] + lam * P[s][j + 1]
                dM = M1 - M0
                I0 = abs(Q[s][j] - P[s][j])
                I1 = abs(Q[s][j + 1] - P[s][j + 1])
                rhs = (1 - lam) * (I0 + I1)
                if dM < -rhs - 5e-4:      # 4-decimal table granularity
                    viol += 1
                if dM < 0:
                    worst = max(worst, -dM)
                    if rhs > 1e-9:
                        tight = max(tight, -dM / rhs)
        print(name.ljust(24), f"{lam:.2f}", str(viol).rjust(4),
              f"{tight:9.3f}", f"{worst:9.4f}")
        if lam == 0.0:
            falsifier_c[name] = worst
    # per-step X_minus(Q)
    steps = []
    for j in range(1, nT - 1):
        xm = sum(max(0.0, Q[s][j] - Q[s][j + 1]) for s in stems)
        steps.append(xm)
    print(f"  per-step X_minus(Q) (T=5->6 onward): "
          + "  ".join(f"{x:.4f}" for x in steps))

print()
print("FALSIFIER CONSTANTS (lam=0 worst single-record regression per")
print("growth step, this tree/member):",
      {k: round(v, 4) for k, v in falsifier_c.items()})
print("Observable: record-probability regression per refinement step")
print("<= (1-lambda) x (interference on that record); standard")
print("decoherence-based QM predicts 0.  Measured regressions here are")
print("O(0.01-0.2) per step at lam=0 and scale to 0 linearly in (1-lam).")
print("DONE")
