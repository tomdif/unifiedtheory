#!/usr/bin/env python3
r"""
dc_uniqueness_rigorous.py

A RIGOROUS uniqueness detector (replacing the broken dual-support certificate and the
only-generic tie-break), then validation against ground truth, then an adversarial
search aimed at the asymmetric / non-hyperplane region.

Detector. Solve  B* = min Σ_e slack_e(Q)  s.t. Q convex, Q+f convex. The reduced form
is unique up to affine  ⟺  the optimal bending vector b* = slack·Q* is unique (because
slack·Δ = 0 ⟺ Δ affine, so b determines Q mod affine). Test it exactly: for each edge e,
maximize and minimize (slack·Q)_e over the optimal face {feasible, Σ slack·Q = B*}.
range_e = max - min.  unique ⟺ max_e range_e ≈ 0.   (2E LPs, no genericity.)

Validation: hyperplane functions (x²-y², |x|-|y|) must read UNIQUE; this also settles
the non-hyperplane cases (x³-3xy², checkerboard) that the broken certificate flagged.
"""
import itertools
import numpy as np
from scipy.optimize import linprog
np.set_printoptions(suppress=True, precision=4)


def grid2d(m):
    V = [(i, j) for j in range(m) for i in range(m)]
    idx = {v: k for k, v in enumerate(V)}
    tris = []
    for j in range(m-1):
        for i in range(m-1):
            a, b, c, d = idx[(i,j)], idx[(i+1,j)], idx[(i+1,j+1)], idx[(i,j+1)]
            tris += ([(a,b,d),(b,c,d)] if (i+j) % 2 == 0 else [(a,b,c),(a,c,d)])
    from collections import defaultdict
    em = defaultdict(list)
    for t in tris:
        a, b, c = t
        for (u, v, w) in [(a,b,c),(b,c,a),(c,a,b)]:
            em[frozenset((u,v))].append((u, v, w))
    inter = [(tuple(e), l[0][2], l[1][2]) for e, l in em.items() if len(l) == 2]
    return np.array([(x,y) for x,y in V], float), tris, inter


def plane_row(pts, simplex, w, V):
    M = np.column_stack([pts[list(simplex)], np.ones(len(simplex))])
    coeff = np.append(pts[w], 1.0) @ np.linalg.inv(M)
    row = np.zeros(V)
    for cc, vtx in zip(coeff, simplex):
        row[vtx] += cc
    return row


def build(pts, tris, inter):
    V = len(pts)
    conv = []
    for t in tris:
        ts = set(t)
        for w in range(V):
            if w in ts: continue
            r = np.zeros(V); r[w] += 1.0; r -= plane_row(pts, t, w, V); conv.append(r)
    slack = []
    for (e, c1, c2) in inter:
        r = np.zeros(V); r[c2] += 1.0; r -= plane_row(pts, tuple(e)+(c1,), c2, V); slack.append(r)
    return np.array(conv), np.array(slack)


def rigorous_range(conv, slack, h):
    """returns max over edges of the bending-coordinate range on the optimal face."""
    V = conv.shape[1]
    cf = conv @ h
    A_ub = np.vstack([-conv, -conv]); b_ub = np.concatenate([np.zeros(conv.shape[0]), cf])
    csum = slack.sum(0)
    r0 = linprog(csum, A_ub=A_ub, b_ub=b_ub, bounds=[(None, None)]*V, method="highs")
    if not r0.success:
        return None
    Bstar = float(csum @ r0.x)
    # optimal face: feasible AND total bending <= Bstar (+tol)
    A_face = np.vstack([A_ub, csum]); b_face = np.append(b_ub, Bstar + 1e-9)
    worst = 0.0
    for e in range(slack.shape[0]):
        hi = linprog(-slack[e], A_ub=A_face, b_ub=b_face, bounds=[(None, None)]*V, method="highs")
        lo = linprog(slack[e],  A_ub=A_face, b_ub=b_face, bounds=[(None, None)]*V, method="highs")
        if hi.success and lo.success:
            worst = max(worst, float(slack[e] @ hi.x) - float(slack[e] @ lo.x))
    return worst


m = 5
pts, tris, inter = grid2d(m)
conv, slack = build(pts, tris, inter)
V = len(pts)
xs = pts[:,0]/(m-1)*2-1; ys = pts[:,1]/(m-1)*2-1
print(f"2D mesh {m}x{m}: V={V}, interior edges={len(inter)}; detector = 2·{len(inter)} LPs/f\n")

# ---- VALIDATION ----
val = [
    ("x²-y²  (hyperplane, proven unique)", xs*xs - ys*ys),
    ("|x|-|y| (hyperplane, proven unique)", np.abs(xs) - np.abs(ys)),
    ("x³-3xy² (outside; cert had flagged it)", xs**3 - 3*xs*ys*ys),
    ("checkerboard cos·cos (outside)", np.cos(np.pi*xs)*np.cos(np.pi*ys)),
]
print("VALIDATION (rigorous bending-face extent):")
for name, h in val:
    rng = rigorous_range(conv, slack, np.asarray(h, float))
    print(f"  {name:<42} max bending-range = {rng:.3e}  -> "
          f"{'UNIQUE' if rng < 1e-6 else 'NON-UNIQUE'}")

# ---- ADVERSARIAL SEARCH: asymmetric, non-hyperplane f ----
print("\nADVERSARIAL SEARCH (asymmetric non-separable f, rigorous detector):")
rng_gen = np.random.default_rng(0)
best = (-1.0, None)
N = 400
for k in range(N):
    if k % 3 == 0:
        h = rng_gen.standard_normal(V)                                  # fully random
    elif k % 3 == 1:                                                     # asymmetric non-separable poly
        a = rng_gen.standard_normal(6)
        h = a[0]*xs*ys + a[1]*xs*xs*ys + a[2]*xs*ys*ys + a[3]*xs**3 + a[4]*ys**3 + a[5]*xs*ys*(xs+ys)
    else:                                                               # random + symmetry-breaking jitter
        h = (xs**3 - 3*xs*ys*ys) + 0.4*rng_gen.standard_normal(V)
    r = rigorous_range(conv, slack, h)
    if r is not None and r > best[0]:
        best = (r, h.copy())
print(f"  searched {N} asymmetric f;  MAX bending-range found = {best[0]:.3e}")
if best[0] < 1e-6:
    print("  -> rigorous detector finds NO non-uniqueness on this fixed mesh.")
    print("     (Consistent with: non-uniqueness, if it exists, needs OFF-MESH creases —")
    print("      P,Q on a finer complex than f. That is the next test.)")
else:
    print(f"  -> CANDIDATE non-unique f found (range {best[0]:.3e}); verify explicitly.")
