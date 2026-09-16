"""Look-elsewhere test for alpha(0) = ln(5/3)/70.

FineStructureIRFromGap.lean promotes the closed form partly on UNIQUENESS:
over p/q, sqrt(p/q) (p,q 7-smooth <= 5000) and gamma4/q, gamma4/70 is the only
form within 0.0021% of alpha(0). Being the best of a family is guaranteed for
some member, so uniqueness is not significance. The question here is:

  For a structureless target of the same size as alpha, how often does the
  same family produce a hit at least this close?

Null: target t = alpha * exp(u), u ~ Uniform(-ln 2, ln 2) (log-uniform over an
octave-scale window around alpha). Hit = some family member within the
observed relative error eps = |pred - CODATA| / CODATA.
"""
import json
import math

import numpy as np

ALPHA_INV = 137.035999177  # CODATA 2022
ALPHA = 1.0 / ALPHA_INV
G4 = math.log(5 / 3)
EPS = abs(70 / G4 - ALPHA_INV) / ALPHA_INV
N_TARGETS = 200_000
RNG = np.random.default_rng(20260916)


def smooth7(limit):
    out = set()
    for a in range(14):
        for b in range(9):
            for c in range(6):
                for d in range(5):
                    n = 2**a * 3**b * 5**c * 7**d
                    if n <= limit:
                        out.add(n)
    return np.array(sorted(out), dtype=float)


S = smooth7(5000)
logS = np.log(S)
ratios = np.unique((logS[:, None] - logS[None, :]).ravel())  # log(p/q)

FAMILIES = {
    "gamma4/q (the promoted form's family)": np.log(G4) - logS,
    "p/q": ratios,
    "sqrt(p/q)": ratios / 2,
    "gamma4*p/q": np.log(G4) + ratios,
}
FAMILIES["recorded search: p/q U sqrt(p/q) U gamma4/q"] = np.unique(
    np.concatenate([FAMILIES["gamma4/q (the promoted form's family)"],
                    FAMILIES["p/q"], FAMILIES["sqrt(p/q)"]]))


def min_log_err(fam, logt):
    fam = np.sort(fam)
    i = np.clip(np.searchsorted(fam, logt), 1, len(fam) - 1)
    return np.minimum(np.abs(fam[i] - logt), np.abs(fam[i - 1] - logt))


logt = math.log(ALPHA) + RNG.uniform(-math.log(2), math.log(2), N_TARGETS)
tol = math.log1p(EPS)
res = {"eps_rel": EPS, "n_7smooth": int(len(S)), "families": {}}
for name, fam in FAMILIES.items():
    fam = fam[np.isfinite(fam)]
    p = float(np.mean(min_log_err(fam, logt) <= tol))
    res["families"][name] = {"size": int(len(fam)), "p_hit": p}

# trials over observables the program has scanned with gamma4 forms
# (FineStructureIRFromGap scope note: alpha(0), alpha(M_Z), alpha ratio,
# sin^2 thetaW, alpha_s, >=2 cosmological Omegas -> at least 7).
for N in (7, 20):
    res[f"global_p_N{N}"] = {
        k: 1 - (1 - v["p_hit"]) ** N for k, v in res["families"].items()}

print(json.dumps(res, indent=2))
json.dump(res, open("alpha_look_elsewhere.json", "w"), indent=2)
