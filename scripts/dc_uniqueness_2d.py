#!/usr/bin/env python3
r"""
dc_uniqueness_2d.py

Open question: does the 1D "reduced DC decomposition is unique" theorem survive to 2D?

1D fact: f'' = signed measure μ; reduced f = P-Q has P'' = μ₊, Q'' = μ₋ (Jordan,
UNIQUE). 2D obstruction: curvature of a PL function lives on EDGES (slack_e per
interior edge), and the edge-slacks are NOT independent — they satisfy cycle
constraints (E > V). So the facewise-Jordan assignment slack_e(P) = (λ_e)₊ is
generally cycle-infeasible; the minimal-curvature compromise can have TIES.

We test it directly. For a PL function f on a triangulated grid:

  variable: Q (vertex heights), P := Q + f.
  reduced/minimal DC  =  min Σ_e slack_e(Q)   (total convex bending of Q)
       s.t.  slack_e(Q) ≥ 0          (Q convex)
             slack_e(Q) ≥ -λ_e(f)    (P = Q+f convex)
  i.e. slack_e(Q) ≥ (λ_e(f))₋ =: d_e ,  with slack_e a linear functional of Q.

slack_e is invariant under adding an affine function to Q, so the objective is
gauge-invariant; the optimal Q is determined only up to affine. NON-UNIQUENESS
BEYOND AFFINE  ⟺  the reduced DC form is not unique  ⟺  a 2D counterexample.

We detect a >0-dimensional optimal face by re-solving with two tiny random
objective tie-breakers and checking the two optima differ by more than an affine
function.
"""
import numpy as np
from scipy.optimize import linprog
np.set_printoptions(suppress=True, precision=4)


# ---------- triangulated grid ----------
def build_grid(m):
    """m x m vertices on integer grid; each cell split by the (i+j) parity diagonal."""
    V = [(i, j) for j in range(m) for i in range(m)]
    idx = {v: k for k, v in enumerate(V)}
    tris = []
    for j in range(m - 1):
        for i in range(m - 1):
            a, b, c, d = idx[(i, j)], idx[(i+1, j)], idx[(i+1, j+1)], idx[(i, j+1)]
            if (i + j) % 2 == 0:
                tris += [(a, b, d), (b, c, d)]
            else:
                tris += [(a, b, c), (a, c, d)]
    # interior edges shared by 2 triangles -> (a,b)=shared, c,d = the two apexes
    from collections import defaultdict
    edgemap = defaultdict(list)
    for t in tris:
        a, b, c = t
        for (u, v, w) in [(a, b, c), (b, c, a), (c, a, b)]:
            edgemap[frozenset((u, v))].append((u, v, w))
    inter = []
    for e, lst in edgemap.items():
        if len(lst) == 2:
            (u, v, c1), (_, _, c2) = lst
            u, v = tuple(e)
            inter.append((u, v, c1, c2))
    return np.array([(x, y) for (x, y) in V], float), tris, inter


def slack_row(pts, a, b, c, d, V):
    """linear functional  z_d - plane_{a,b,c}(d)  as a length-V row (convex bending across edge ab)."""
    P = np.array([[pts[a,0], pts[a,1], 1],
                  [pts[b,0], pts[b,1], 1],
                  [pts[c,0], pts[c,1], 1]], float)
    w = np.array([pts[d,0], pts[d,1], 1.0])
    coeff = np.linalg.solve(P.T, w)     # plane_{abc}(d) = coeff·(z_a,z_b,z_c)
    row = np.zeros(V); row[d] = 1.0
    row[a] -= coeff[0]; row[b] -= coeff[1]; row[c] -= coeff[2]
    return row


def affine_residual(pts, delta):
    """norm of delta after removing best-fit affine (alpha + beta x + gamma y)."""
    A = np.column_stack([np.ones(len(pts)), pts[:,0], pts[:,1]])
    coef, *_ = np.linalg.lstsq(A, delta, rcond=None)
    return np.linalg.norm(delta - A @ coef)


def reduced_dc(pts, inter, h, tie=None):
    V = len(pts)
    S = np.array([slack_row(pts, a, b, c, d, V) for (a, b, c, d) in inter])  # E x V
    lam_f = S @ h                       # curvature of f per edge
    d_e = np.maximum(-lam_f, 0.0)       # lower bounds (P=Q+f convex)
    c = S.sum(axis=0).astype(float)     # objective: Σ_e slack_e(Q)
    if tie is not None:
        c = c + tie
    # constraints  slack_e(Q) ≥ max(0, d_e)  ->  -S Q ≤ -lb
    lb = np.maximum(d_e, 0.0)
    res = linprog(c, A_ub=-S, b_ub=-lb, bounds=[(None, None)]*V, method="highs")
    return res, S, lam_f, lb


def analyze(name, m, h):
    pts, tris, inter = build_grid(m)
    res0, S, lam_f, lb = reduced_dc(pts, inter, h)
    assert res0.success, "LP infeasible"
    obj_true = float(S.sum(0) @ res0.x)
    nconc = int((lam_f < -1e-9).sum()); nconv = int((lam_f > 1e-9).sum())
    print(f"\n=== {name}  (grid {m}x{m}: V={len(pts)}, edges={len(inter)}) ===")
    print(f"    f curvature: {nconv} convex creases, {nconc} concave creases")
    print(f"    min total bending Σ slack_e(Q) = {obj_true:.6f}")

    # probe optimal-face dimension with two tiny random tie-breakers
    rng = np.random.default_rng(0)
    eps = 1e-4 * (abs(obj_true) + 1)
    sols = []
    for s in range(6):
        tie = eps * rng.standard_normal(S.shape[0]) @ S
        r, *_ = reduced_dc(pts, inter, h, tie=tie)
        if r.success and float(S.sum(0) @ r.x) <= obj_true + 50*eps:
            sols.append(r.x)
    # pairwise non-affine distance among optima
    worst = 0.0; pair = None
    for i in range(len(sols)):
        for j in range(i+1, len(sols)):
            rdist = affine_residual(pts, sols[i] - sols[j])
            if rdist > worst:
                worst = rdist; pair = (sols[i], sols[j])
    unique = worst < 1e-6
    print(f"    optimal Q non-affine spread across tie-breaks = {worst:.3e}"
          f"   -> {'UNIQUE (mod affine)' if unique else 'NON-UNIQUE -> counterexample'}")
    return pts, inter, S, lam_f, h, obj_true, (None if unique else pair)


# ---------- helper: sample a height field, then test ----------
def field(m, fn):
    pts, *_ = build_grid(m)
    xs = pts[:,0] / (m-1) * 2 - 1
    ys = pts[:,1] / (m-1) * 2 - 1
    return np.array([fn(x, y) for x, y in zip(xs, ys)], float)


tests = [
    ("convex bowl  x²+y² (control)", 4, lambda m: field(m, lambda x, y: x*x + y*y)),
    ("saddle  x²-y²",               4, lambda m: field(m, lambda x, y: x*x - y*y)),
    ("4-fold |x|-|y|",              5, lambda m: field(m, lambda x, y: abs(x) - abs(y))),
    ("symmetric monkey  x³-3xy²",   5, lambda m: field(m, lambda x, y: x**3 - 3*x*y*y)),
    ("checkerboard bumps",          5, lambda m: field(m, lambda x, y: np.cos(np.pi*x)*np.cos(np.pi*y))),
]

found = None
for name, m, hf in tests:
    out = analyze(name, m, hf(m))
    if out[-1] is not None and found is None:
        found = (name, *out)

# ---------- if a counterexample was found, verify it explicitly ----------
if found:
    name, pts, inter, S, lam_f, h, obj_true, (Q1, Q2) = found
    print("\n" + "=" * 60)
    print(f"COUNTEREXAMPLE found on: {name}")
    print("=" * 60)
    for tag, Q in [("Q1", Q1), ("Q2", Q2)]:
        P = Q + h
        sQ = S @ Q; sP = S @ P
        convQ = sQ.min() >= -1e-7; convP = sP.min() >= -1e-7
        diff_is_f = np.allclose(P - Q, h, atol=1e-9)
        tot = sQ.sum()
        print(f"  {tag}: Q convex={convQ}  P=Q+f convex={convP}  P-Q==f={diff_is_f}  "
              f"total bending={tot:.6f}")
    rdist = affine_residual(pts, Q1 - Q2)
    print(f"  Q1, Q2 differ by a NON-affine function: residual={rdist:.4e}  (both minimal)")
    print("  => two distinct reduced DC decompositions of the same f.")
    print("  => reduced-DC uniqueness FAILS in 2D.  The 1D theorem does NOT lift.")
else:
    print("\nNo counterexample in this battery — reduced DC appeared unique (mod affine).")
