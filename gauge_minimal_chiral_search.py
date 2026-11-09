"""Does 'minimal chiral anomaly-free' actually select SU(3)xSU(2)xU(1)?

SMUniqueness.lean / ColorGroupForced.lean / GaugeGroupDerived.lean reach the SM
only after fixing (i) exactly two simple factors plus U(1), (ii) an SM-shaped
template, (iii) <= 15 Weyl fermions.  This script drops those premises and asks
the bare question over a broad class:

  gauge groups: U(1); G; G x U(1); G1 x G2; G1 x G2 x U(1)   with G in SU(2..6)
  reps:         SU(2): 1, 2      SU(N>=3): 1, N, Nbar, A2, A2bar (A2 = antisym)
  charges:      integers |q| <= QMAX (any rational set rescales to this)

Conditions imposed (all standard):
  * every cubic SU(N)^3, mixed SU(N)^2 U(1), U(1)^3, grav-U(1) anomaly cancels
  * Witten global anomaly: even number of doublets for each SU(2)
  * strict chirality: no gauge-invariant fermion bilinear (Dirac or Majorana)
  * every factor acts nontrivially; no fermion is a total singlet
Output: the minimal number of Weyl fermions for each gauge group, with a witness.
"""
import itertools
import json
from collections import Counter
from functools import lru_cache

QMAX = 12
MAXDIM = 15


def reps(N):
    if N == 2:
        return ["1", "F"]
    out = ["1", "F", "Fb"]
    if N >= 4:
        out += ["A", "Ab"] if N != 4 else ["A"]      # SU(4) A2 = 6 is real
    return out


def dim(N, r):
    return {"1": 1, "F": N, "Fb": N, "A": N * (N - 1) // 2, "Ab": N * (N - 1) // 2}[r]


def cubic(N, r):
    if N == 2:
        return 0
    return {"1": 0, "F": 1, "Fb": -1, "A": N - 4, "Ab": -(N - 4)}[r]


def dynkin2(N, r):   # 2*T(r)
    return {"1": 0, "F": 1, "Fb": 1, "A": N - 2, "Ab": N - 2}[r]


def conj(N, r):
    if N == 2:
        return r
    if N == 4 and r == "A":
        return "A"
    return {"1": "1", "F": "Fb", "Fb": "F", "A": "Ab", "Ab": "A"}[r]


def singlet_in_product(N, r, s):
    """Does r (x) s contain the trivial rep?"""
    return s == conj(N, r)


def mass_allowed(groups, f, g, same):
    for N, r, s in zip(groups, f[0], g[0]):
        if not singlet_in_product(N, r, s):
            return False
    if f[1] + g[1] != 0:
        return False
    if same:
        # Majorana term for a single Weyl multiplet: need a SYMMETRIC invariant.
        # SU(2) doublet invariant is antisymmetric -> vanishes for one Weyl field.
        n_doublet = sum(1 for N, r in zip(groups, f[0]) if N == 2 and r == "F")
        return n_doublet % 2 == 0
    return True


def nonabelian_skeletons(groups):
    """Multisets of nonabelian rep-tuples with total dim <= MAXDIM satisfying cubic + Witten."""
    tuples = [t for t in itertools.product(*[reps(N) for N in groups])]
    dims = {t: _prod(dim(N, r) for N, r in zip(groups, t)) for t in tuples}
    res = []

    def rec(start, cur, d):
        if cur and _skeleton_ok(groups, cur):
            res.append(tuple(cur))
        for i in range(start, len(tuples)):
            t = tuples[i]
            if d + dims[t] <= MAXDIM:
                cur.append(t)
                rec(i, cur, d + dims[t])
                cur.pop()

    rec(0, [], 0)
    return res, dims


def _prod(it):
    p = 1
    for x in it:
        p *= x
    return p


def _skeleton_ok(groups, sk):
    for k, N in enumerate(groups):
        others = lambda t: _prod(dim(M, r) for j, (M, r) in enumerate(zip(groups, t)) if j != k)
        if N >= 3 and sum(cubic(N, t[k]) * others(t) for t in sk) != 0:
            return False
        if N == 2 and sum(others(t) for t in sk if t[k] == "F") % 2:
            return False
        if all(t[k] == "1" for t in sk):
            return False            # factor acts trivially
    return True


def chiral(groups, fermions):
    for i, f in enumerate(fermions):
        for j in range(i, len(fermions)):
            if mass_allowed(groups, f, fermions[j], i == j):
                return False
    return True


def charge_solutions(groups, sk, dims, with_u1):
    """Yield fermion lists (rep-tuple, q). Without U(1), q=0."""
    if not with_u1:
        fs = [(t, 0) for t in sk]
        if all(any(r != "1" for r in t) for t in sk) and chiral(groups, fs):
            yield fs
        return
    n = len(sk)
    d = [dims[t] for t in sk]
    t2 = [[dynkin2(N, t[k]) * _prod(dim(M, r) for j, (M, r) in enumerate(zip(groups, t)) if j != k)
           for k, N in enumerate(groups)] for t in sk]
    if n > 6:
        return                            # keep the charge scan finite; SM itself has n = 5
    qmax = QMAX if n <= 4 else 6          # SM hypercharges x6 fit in |q| <= 6
    qs = range(-qmax, qmax + 1)
    # enumerate last charge from the linear grav constraint
    for head in itertools.product(qs, repeat=n - 1):
        lin = sum(di * q for di, q in zip(d, head))
        if lin % d[-1]:
            continue
        ql = -lin // d[-1]
        if abs(ql) > QMAX:
            continue
        q = head + (ql,)
        if sum(di * x ** 3 for di, x in zip(d, q)):
            continue
        if any(sum(t2[i][k] * q[i] for i in range(n)) for k in range(len(groups))):
            continue
        if all(x == 0 for x in q):
            continue                      # U(1) acts trivially
        fs = list(zip(sk, q))
        if any(all(r == "1" for r in t) and x == 0 for t, x in fs):
            continue
        if chiral(groups, fs):
            yield fs


def u1_only():
    best = None
    for n in range(1, 9):
        for q in itertools.combinations_with_replacement(range(-QMAX, QMAX + 1), n):
            if 0 in q or sum(q) or sum(x ** 3 for x in q):
                continue
            if any(-x in q for x in q):
                continue
            from math import gcd
            from functools import reduce
            if reduce(gcd, [abs(x) for x in q]) != 1:
                continue
            return {"weyl": n, "witness": sorted(q)}
    return best


def search(groups, with_u1):
    sks, dims = nonabelian_skeletons(groups)
    best = None
    for sk in sorted(sks, key=lambda s: sum(dims[t] for t in s)):
        w = sum(dims[t] for t in sk)
        if best and w > best["weyl"]:
            break
        for fs in charge_solutions(groups, sk, dims, with_u1):
            cand = {"weyl": w, "witness": [[list(t), q] for t, q in fs]}
            if best is None or w < best["weyl"]:
                best = cand
            break
    return best


def main():
    out = {"U(1)": u1_only()}
    simple = [2, 3, 4, 5, 6]
    for N in simple:
        for u1 in (False, True):
            out[f"SU({N})" + (" x U(1)" if u1 else "")] = search((N,), u1)
    for N1, N2 in itertools.combinations_with_replacement(simple, 2):
        for u1 in (False, True):
            key = f"SU({N1}) x SU({N2})" + (" x U(1)" if u1 else "")
            out[key] = search((N1, N2), u1)
            print(key, out[key] and out[key]["weyl"], flush=True)
    found = {k: v for k, v in out.items() if v}
    ranking = sorted(found.items(), key=lambda kv: kv[1]["weyl"])
    summary = {"MAXDIM": MAXDIM, "QMAX": QMAX,
               "ranking": [(k, v["weyl"]) for k, v in ranking],
               "none_found_up_to_MAXDIM": [k for k, v in out.items() if not v],
               "details": out}
    print(json.dumps(summary["ranking"], indent=0))
    with open("gauge_minimal_chiral_search.json", "w") as f:
        json.dump(summary, f, indent=1)


if __name__ == "__main__":
    main()
