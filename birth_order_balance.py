#!/usr/bin/env python3
"""Birth-order balance of the pi/4 Born chain vs the 1/3-2/3 bounds.

Motivation: Kahn-Saks / Brightwell-Felsner-Trotter / Aires-Chan-Pak-Panova (2026) bound
P(x<y) in a UNIFORM random linear extension.  In sequential growth, birth orders of a
final causet C are exactly its linear extensions, and Rideout-Sorkin covariance means
the conditional distribution over them is uniform.  AUDIT_COVARIANCE.md proves the pi/4
dynamics is NOT strictly covariant (covariance_no_go), so its conditional birth-order
law can differ.  This measures by how much, exactly, at n = 8.

Exact method: the Born chain is Markov on labeled causets and each labeled step
D -> D+{v} has weight |rho(class D, class D+v)|^2.  For each final class C, a DP over
the downset lattice of C gives forward/backward weights; P(x before y | C) is then exact.

Per C (non-chain), over incomparable pairs:
  delta(C) = max_{x||y} min(P(x<y), P(y<x))          (Kahn-Saks balance)
Covariant theorems (uniform extensions, all finite non-chain posets):
  delta >= (5-sqrt5)/10 = 0.2764 (BFT 1995; +eps, ACPP 2026); delta >= 1/3 verified
  computationally for all posets on <= 11 elements (so exactly true at n = 8).
Readings (registered before the run):
  (C) COVARIANT-LIKE: pi/4 delta >= 1/3 on every supported C, max|P_law - P_unif| small
  (V) VIOLATES: some supported C has delta_law < 1/3 (a birth-order asymmetry that no
      covariant law can produce); report Born mass on such C and the minimum delta
  (S) SHARPLY VIOLATES: some C has delta_law < 0.2764 (below the BFT theorem floor)
Controls: transitive percolation p=1/2 (covariant => must equal uniform to ~1e-15);
          uniform labeled growth (the counting baseline, also non-covariant).
"""
import math, sys, time, itertools
import numpy as np

SRC = open("pi4_first_prediction.py").read()
exec(SRC.split('log("=== LAW 1: max-entropy selection ===")')[0])   # engine + feasibility + build_law

BFT = (5 - math.sqrt(5)) / 10
N8 = NMAX
_ccache = {}
def cls_of(sub, rel_by_elem):
    """canonical class of induced subposet on element set sub (frozenset)."""
    els = sorted(sub); idx = {e: i for i, e in enumerate(els)}
    r = tuple(sorted((idx[a], idx[b]) for (a, b) in rel_by_elem if a in sub and b in sub))
    k = (len(els), r)
    if k not in _ccache: _ccache[k] = canon_fast(len(els), r) if els else None
    return _ccache[k]

def analyse(C, stepw):
    """stepw(prefix_cls, child_cls, D, v, rel) -> weight.  returns (Z, P matrix over pairs)."""
    m, rel = levels[N8][C]
    below = {x: frozenset(a for (a, b) in rel if b == x) for x in range(m)}
    downs = [frozenset(D) for D in downsets_of(m, rel)]
    downs.sort(key=len)
    cl = {D: cls_of(D, rel) for D in downs}
    F = {frozenset(): 1.0}
    edges = []
    for D in downs:
        if D not in F: F[D] = 0.0
        for v in range(m):
            if v in D or not below[v] <= D: continue
            E = D | {v}
            w = stepw(cl[D], cl[E], D, v, rel) if D else 1.0   # first element: root is forced
            edges.append((D, v, E, w))
    for D, v, E, w in edges:   # downs sorted by size -> edges in topological order
        F[E] = F.get(E, 0.0) + F[D] * w
    B = {D: 0.0 for D in downs}; full = frozenset(range(m)); B[full] = 1.0
    for D, v, E, w in reversed(edges):
        B[D] += w * B[E]
    Z = F[full]
    # P(x born before y) = sum over steps adding x from D with y not in D
    P = np.zeros((m, m))
    if Z > 0:
        for D, v, E, w in edges:
            flow = F[D] * w * B[E] / Z
            for y in range(m):
                if y != v and y not in D: P[v, y] += flow
    related = {(a, b) for (a, b) in rel}
    return Z, P, related

def delta_stats(P, related, m):
    inc = [(x, y) for x in range(m) for y in range(x + 1, m)
           if (x, y) not in related and (y, x) not in related]
    if not inc: return None, inc
    return max(min(P[x, y], P[y, x]) for x, y in inc), inc

# step-weight functions -------------------------------------------------------
def born_w(law):
    return lambda pc, cc, D, v, rel: abs(law.get((pc, cc), 0.0)) ** 2
Kpar = {p: sum(mu for _, (mu, g) in children[p].items()) for p in parents}
unif_growth_w = lambda pc, cc, D, v, rel: 1.0 / Kpar[pc]
def perc_w(pc, cc, D, v, rel, p=0.5):
    past = {a for (a, b) in rel if b == v}
    maxl = {a for a in past if not any((a, c) in rel for c in past)}
    return p ** len(maxl) * (1 - p) ** (len(D) - len(past))
flat_w = lambda pc, cc, D, v, rel: 1.0      # uniform over linear extensions

_ucache = {}
def run(tag, stepw, Wborn=None):
    rows = []
    t = time.time()
    for C in sorted(levels[N8]):
        m, rel = levels[N8][C]
        if C not in _ucache:
            _, Pu, related = analyse(C, flat_w); _ucache[C] = (Pu, related, *delta_stats(Pu, related, m))
        Pu, related, du, inc = _ucache[C]
        if du is None: continue                      # chain
        Z, P, _ = analyse(C, stepw)
        if Z <= 0: continue                          # C not in this law's support
        dl, _ = delta_stats(P, related, m)
        dev = max(abs(P[x, y] - Pu[x, y]) for x, y in inc)
        det = sum(1 for x, y in inc if min(P[x, y], P[y, x]) < 1e-12)
        rows.append(dict(C=C, d_unif=du, d_law=dl, dev=dev, n_inc=len(inc), n_det=det,
                         w=(Wborn.get(C, 0.0) if Wborn else 1.0), Z=Z))
    W = sum(r["w"] for r in rows)
    below13 = [r for r in rows if r["d_law"] < 1 / 3 - 1e-12]
    belowB = [r for r in rows if r["d_law"] < BFT - 1e-12]
    anydet = [r for r in rows if r["n_det"] > 0]
    log(f"[{tag}] {len(rows)} supported non-chain C at n={N8}  ({time.time()-t:.0f}s)")
    log(f"   uniform delta: min {min(r['d_unif'] for r in rows):.4f}  (sanity: must be >= 1/3)")
    log(f"   law delta:     min {min(r['d_law'] for r in rows):.4f}  "
        f"weighted-mean {sum(r['w']*r['d_law'] for r in rows)/W:.4f}  "
        f"(uniform weighted-mean {sum(r['w']*r['d_unif'] for r in rows)/W:.4f})")
    log(f"   max |P_law - P_unif| over all pairs: {max(r['dev'] for r in rows):.3e}  "
        f"weighted-mean per C {sum(r['w']*r['dev'] for r in rows)/W:.4f}")
    log(f"   C with delta_law < 1/3:     {len(below13)} (mass {sum(r['w'] for r in below13)/W:.4f})")
    log(f"   C with delta_law < {BFT:.4f}: {len(belowB)} (mass {sum(r['w'] for r in belowB)/W:.4f})")
    log(f"   C with a DETERMINISTIC spacelike birth order (P=0/1): {len(anydet)} "
        f"(mass {sum(r['w'] for r in anydet)/W:.4f})")
    worst = sorted(rows, key=lambda r: r["d_law"])[:3]
    for r in worst:
        log(f"   worst: delta_law {r['d_law']:.4f} vs unif {r['d_unif']:.4f}  rel={r['C'][1]}  mass-weight {r['w']:.2e}")
    return rows

def born_W(law):
    W = {root: 1.0}
    for key in allkeys:
        W.setdefault(key, 0.0)
    for p in allkeys:
        for ck, (mu, g) in children.get(p, {}).items():
            if (p, ck) in law: W[ck] += W[p] * mu * abs(law[(p, ck)]) ** 2
    return W

log("=== CONTROL: transitive percolation p=1/2 (covariant) ===")
run("percolation", perc_w)
log("=== BASELINE: uniform labeled growth (non-covariant counting) ===")
lawU = {(p, ck): math.sqrt(1.0 / Kpar[p]) for p in parents for ck in children[p]}
run("uniform growth", unif_growth_w, born_W(lawU))
log("=== pi/4 max-entropy law ===")
law_me, _ = build_law("maxent")
run("pi/4 maxent", born_w(law_me), born_W(law_me))
for i in range(2):
    log(f"=== pi/4 random selection {i} ===")
    law_r, _ = build_law("random")
    run(f"pi/4 random {i}", born_w(law_r), born_W(law_r))
log("DONE")
