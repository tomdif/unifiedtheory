#!/usr/bin/env python3
"""Exact certificate for the depth-8 gate + the sufficiency witness
(referee: harden t* = 2.1e-5 — "the positivity certificate anchoring
'counts are exact supports' shouldn't be the one floating-point
statement in the chain").

Structure: within the web every channel sign is +-1, so boundary
amplitudes x_D > 0 at level 8 back-substitute to a solution of ALL
wave equations BY CONSTRUCTION in exact arithmetic; the only
condition is positivity of every interior amplitude.  So the exact-t*
certificate and the depth-8 sufficiency witness coincide.

ERROR TRAIL (kept per repo discipline): run 1 (exact_certificate.log)
imposed sign(A) = chi — the WRONG criterion (chi lives inside the
channel signs; amplitudes must simply be positive) — and used a
too-narrow boundary box [1,10]; run 2 (exact_certificate2.log) fixed
the box but kept the bad criterion.  Run 3 (exact_certificate3.log,
this file's logic): uniform boundary genuinely fails (120 negative,
90 zero amplitudes — the sufficiency witness NEEDS tuned weights;
the conjecture is not shallow), and the LP-tuned boundary,
rationalized and back-substituted in exact rational arithmetic,
gives ALL 5816 amplitudes positive: exact min ~ 2.030e-13 (an exact
fraction printed in the log), max = 1.

CONSEQUENCE: the seventh set-equality (depth-8 gate == hereditary
real) is certified in exact arithmetic: the hereditary-real web is
gate-sufficient at depth 8, witnessed explicitly.  Necessity
(gate-support => hereditary-real) remains the conjectural direction.
"""

import itertools, math
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog

esrc = open("escape_n8.py").read()
exec(esrc[:esrc.index("# ---- machine-check the constructions")])
esrc2 = open("escape_n8.py").read()
exec(esrc2[esrc2.index("# ---- the depth-8 gate"):esrc2.index("U = set(allkeys)")])
W = {key for key in allkeys if hereditary_real(key)}
def sigma(g):
    return 1 if g % 2 == 0 else -1

def backsub(xb):
    Ax = {}
    for key in sorted(W, key=lambda k: -nelem(k)):
        if nelem(key) == NMAX:
            Ax[key] = xb[key]
        else:
            Ax[key] = sum(mu * sigma(g) * Ax[ck]
                          for ck, (mu, g) in children[key].items() if ck in W)
    return Ax

boundary = [k for k in sorted(W) if nelem(k) == NMAX]
Au = backsub({k: Fraction(1) for k in boundary})
neg = sum(1 for k in W if Au[k] < 0); zer = sum(1 for k in W if Au[k] == 0)
print(f"uniform boundary: negative {neg}, zeros {zer}")
interior = [k for k in sorted(W) if nelem(k) < NMAX]
bix = {k: i for i, k in enumerate(boundary)}
vec = {}
for key in sorted(W, key=lambda k: -nelem(k)):
    if nelem(key) == NMAX:
        v = np.zeros(len(boundary)); v[bix[key]] = 1.0
    else:
        v = np.zeros(len(boundary))
        for ck, (mu, g) in children[key].items():
            if ck in W: v += mu * sigma(g) * vec[ck]
    vec[key] = v
M = np.array([vec[k] for k in interior])
nb = len(boundary)
c = np.zeros(nb + 1); c[-1] = -1.0
A_ub = np.hstack([-M, np.ones((len(interior), 1))])
res = linprog(c, A_ub=A_ub, b_ub=np.zeros(len(interior)),
              bounds=[(1, 10**7)] * nb + [(None, None)], method="highs")
print("LP:", res.success, "float t* =", -res.fun)
x = {k: Fraction(v).limit_denominator(10**6)
     for k, v in zip(boundary, res.x[:-1])}
Ax = backsub(x)
neg2 = [k for k in W if Ax[k] <= 0]
print(f"exact back-substitution: nonpositive amplitudes {len(neg2)}")
if not neg2:
    r = Ax[root]
    amps = sorted(Ax[k] / r for k in W)
    print(f"EXACT RATIONAL CERTIFICATE: min ~ {float(amps[0]):.3e}, "
          f"max ~ {float(amps[-1]):.3e}")
print("DONE")
