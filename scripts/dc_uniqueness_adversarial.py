#!/usr/bin/env python3
r"""
dc_uniqueness_adversarial.py

Adversarial search for a counterexample to reduced-DC uniqueness: instead of
spot-checking hand-picked f, hunt over f to find ANY with a non-unique
minimal-total-bending DC decomposition.

Two upgrades over the battery:

  1. EXACT certificate (not random probing). For each f, solve the inner LP, take
     the dual support S = {rows with nonzero dual} (= the constraints tight on the
     whole optimal face), and compute
         face_dim_mod_affine = (V - rank(conv_S)) - (n+1).
     c = Σ_{i∈S} y_i conv_i, so the objective is flat exactly on null(conv_S);
     face_dim_mod_affine > 0  ⟺  non-unique reduced DC  ⟺  counterexample.

  2. ACTIVE search over f: thousands of random height fields (Gaussian, sparse,
     scaled, rank-structured) plus structured "frustrated" families (rotated
     saddles, alternating-sign cycles) designed to create min-cost-flow ties.

Any flagged f is re-confirmed by the provably-sound tie-break test (two optima
differing non-affinely necessarily move some face-slack).
"""
import itertools
import numpy as np
from scipy.optimize import linprog
np.set_printoptions(suppress=True, precision=4)


# ---------------- 2D triangulated grid ----------------
def grid2d(m):
    V = [(i, j) for j in range(m) for i in range(m)]
    idx = {v: k for k, v in enumerate(V)}
    tris = []
    for j in range(m-1):
        for i in range(m-1):
            a, b, c, d = idx[(i,j)], idx[(i+1,j)], idx[(i+1,j+1)], idx[(i,j+1)]
            tris += ([(a,b,d),(b,c,d)] if (i+j) % 2 == 0 else [(a,b,c),(a,c,d)])
    from collections import defaultdict
    fm = defaultdict(list)
    for t in tris:
        for tri in itertools.combinations(t, 2):
            pass
    # interior edges
    em = defaultdict(list)
    for t in tris:
        a, b, c = t
        for (u, v, w) in [(a,b,c),(b,c,a),(c,a,b)]:
            em[frozenset((u,v))].append((u, v, w))
    inter = []
    for e, lst in em.items():
        if len(lst) == 2:
            (u,v,c1),(_,_,c2) = lst
            inter.append((tuple(e), c1, c2))
    return np.array([(x,y) for x,y in V], float), tris, inter


def plane_row(pts, simplex, w, V):
    """plane_{simplex}(r_w) as a length-V row over vertex heights (simplex = d+1 verts)."""
    M = np.column_stack([pts[list(simplex)], np.ones(len(simplex))])
    rw = np.append(pts[w], 1.0)
    coeff = rw @ np.linalg.inv(M)
    row = np.zeros(V)
    for cc, vtx in zip(coeff, simplex):
        row[vtx] += cc
    return row


def build2d(pts, tris, inter):
    V = len(pts)
    conv = []
    for t in tris:
        ts = set(t)
        for w in range(V):
            if w in ts: continue
            r = np.zeros(V); r[w] += 1.0; r -= plane_row(pts, t, w, V)
            conv.append(r)
    slack = []
    for (e, c1, c2) in inter:
        tri = tuple(e) + (c1,)
        r = np.zeros(V); r[c2] += 1.0; r -= plane_row(pts, tri, c2, V)
        slack.append(r)
    return np.array(conv), np.array(slack)


def affine_dim(pts):
    return pts.shape[1] + 1


def inner_lp(conv, slack, h, tie=None):
    V = conv.shape[1]
    cf = conv @ h
    A_ub = np.vstack([-conv, -conv])
    b_ub = np.concatenate([np.zeros(conv.shape[0]), cf])
    c = slack.sum(0).astype(float) + (0 if tie is None else tie)
    return linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=[(None, None)]*V, method="highs")


def face_dim(conv, slack, h, tol=1e-7):
    """exact optimal-face dimension mod affine via dual support."""
    res = inner_lp(conv, slack, h)
    if not res.success:
        return None, res
    duals = np.abs(res.ineqlin.marginals)
    A_ub = np.vstack([-conv, -conv])
    supp = A_ub[duals > tol * max(1.0, duals.max())]
    if supp.shape[0] == 0:
        rank = 0
    else:
        rank = np.linalg.matrix_rank(supp, tol=1e-7)
    V = conv.shape[1]
    return (V - rank) - affine_dim_global, res


def tiebreak_spread(conv, slack, h, pts, seeds=8):
    res0 = inner_lp(conv, slack, h)
    obj = float(slack.sum(0) @ res0.x)
    rng = np.random.default_rng(1)
    eps = 1e-4 * (abs(obj) + 1)
    sols = []
    for _ in range(seeds):
        tie = eps * (rng.standard_normal(slack.shape[0]) @ slack)
        r = inner_lp(conv, slack, h, tie=tie)
        if r.success and float(slack.sum(0) @ r.x) <= obj + 100*eps:
            sols.append(r.x)
    A = np.column_stack([np.ones(len(pts)), pts])
    worst = 0.0
    for i in range(len(sols)):
        for j in range(i+1, len(sols)):
            d = sols[i]-sols[j]
            coef,*_ = np.linalg.lstsq(A, d, rcond=None)
            worst = max(worst, np.linalg.norm(d - A@coef))
    return worst


# ---------------- run adversarial search on 2D mesh ----------------
m = 5
pts, tris, inter = grid2d(m)
conv, slack = build2d(pts, tris, inter)
V = len(pts)
affine_dim_global = affine_dim(pts)
print(f"2D mesh {m}x{m}: V={V}, tris={len(tris)}, interior edges={len(inter)}, "
      f"convexity rows={conv.shape[0]}")

rng = np.random.default_rng(0)
xs = pts[:,0]/(m-1)*2-1; ys = pts[:,1]/(m-1)*2-1

best = (-1, None)
n_random = 8000
for k in range(n_random):
    kind = k % 4
    if kind == 0:
        h = rng.standard_normal(V)
    elif kind == 1:                                   # sparse heights
        h = rng.standard_normal(V) * (rng.random(V) < 0.3)
    elif kind == 2:                                   # random low-rank quadratic-ish
        a = rng.standard_normal(5)
        h = a[0]*xs**2 + a[1]*ys**2 + a[2]*xs*ys + a[3]*xs + a[4]*ys
    else:                                             # random saddle rotation, integer-ish
        th = rng.random()*np.pi
        u = np.cos(th)*xs + np.sin(th)*ys; w = -np.sin(th)*xs + np.cos(th)*ys
        h = np.round(u*u - w*w, 0)
    fd, _ = face_dim(conv, slack, h)
    if fd is not None and fd > best[0]:
        best = (fd, h.copy())

# structured frustration families: alternating-sign cycles around the center
for s in range(400):
    th = s/400*2*np.pi
    h = np.sign(np.cos(3*np.arctan2(ys, xs+1e-9) + th)) * (xs**2+ys**2)
    fd, _ = face_dim(conv, slack, h)
    if fd is not None and fd > best[0]:
        best = (fd, h.copy())

print(f"\nadversarial search over {n_random}+400 height fields:")
print(f"  MAX optimal-face dimension (mod affine) found = {best[0]}")
if best[0] <= 0:
    print("  => 0 everywhere: NO counterexample. Reduced DC unique for every f tested.")
else:
    spread = tiebreak_spread(conv, slack, best[1], pts)
    print(f"  => face_dim {best[0]} > 0  CANDIDATE; tie-break spread = {spread:.3e}")
    print("     COUNTEREXAMPLE found" if spread > 1e-6 else "     (cert/tie-break disagree — inspect)")

# sanity: certificate must read 0 on a known-unique case and a control
for name, h in [("saddle x²-y²", xs*xs-ys*ys), ("random", rng.standard_normal(V))]:
    fd, _ = face_dim(conv, slack, np.asarray(h, float))
    print(f"  [check] {name}: face_dim = {fd}")
