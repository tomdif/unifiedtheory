#!/usr/bin/env python3
r"""
dc_uniqueness_3d.py

The genuinely open test: does reduced-DC uniqueness survive to 3D?

Structure is the same LP as 2D (curvature per codim-1 face is SCALAR λ_f in every
dimension — the gradient can only jump along the face normal). What changes in 3D:
codim-1 faces are triangles, and convexity couples at codim-2 = EDGES, where many
tetrahedra meet. That richer codim-2 coupling is where uniqueness could first fail.

To enforce the codim-2 coupling correctly we DO NOT use per-face local convexity;
we use the rigorous GLOBAL convexity test:
      P convex  ⟺  ∀ tet T, ∀ vertex w:  h_w ≥ plane_T(w)
(every linear piece is a global lower-supporting plane = graph is the lower hull).

Mesh: Freudenthal (Kuhn) triangulation of a cube grid — 6 tets/cell, faces match
across cells, fully symmetric (tie-prone, the interesting regime).

LP (Q is the variable, P := Q + f):
   min Σ_faces slack_face(Q)            (total convex bending of Q)
   s.t.  h_w(Q)   ≥ plane_T^Q(w)        ∀T,w   (Q convex, global)
         h_w(Q+f) ≥ plane_T^{Q+f}(w)    ∀T,w   (P convex, global)
Objective is invariant under adding an affine function to Q (affine ⇒ slack 0),
so the optimum is determined only up to affine. NON-UNIQUENESS BEYOND AFFINE
(now 4-dim: 1,x,y,z) = the 3D counterexample.
"""
import itertools
import numpy as np
from scipy.optimize import linprog
np.set_printoptions(suppress=True, precision=4)


# ---------------- Freudenthal tet mesh of a cube grid ----------------
def build_mesh(nx, ny, nz):
    verts = [(i, j, k) for k in range(nz) for j in range(ny) for i in range(nx)]
    idx = {v: t for t, v in enumerate(verts)}
    e = [np.array(v) for v in [(1,0,0),(0,1,0),(0,0,1)]]
    tets = []
    for k in range(nz-1):
        for j in range(ny-1):
            for i in range(nx-1):
                base = np.array((i, j, k))
                for perm in itertools.permutations(range(3)):
                    path = [base.copy()]
                    cur = base.copy()
                    for d in perm:
                        cur = cur + e[d]
                        path.append(cur.copy())
                    tets.append(tuple(idx[tuple(p)] for p in path))
    # interior faces: triangles shared by exactly two tets
    from collections import defaultdict
    fmap = defaultdict(list)
    for t in tets:
        for tri in itertools.combinations(t, 3):
            apex = [v for v in t if v not in tri][0]
            fmap[tuple(sorted(tri))].append((t, apex))
    inter = [(tri, lst[0][1], lst[1][1]) for tri, lst in fmap.items() if len(lst) == 2]
    return np.array(verts, float), tets, inter


def plane_coeffs(pts, tet):
    """affine fit h = a·r + b over a tet's 4 vertices; return length-V row giving plane_T(.) value
       is built per-eval; here return the 4x? — we build slack rows directly instead."""
    M = np.column_stack([pts[list(tet)], np.ones(4)])    # 4x4
    return np.linalg.inv(M)                                # columns map (h0..h3) -> (a,b)


def plane_value_row(pts, tet, w, V):
    """linear functional: plane_T(r_w) as a length-V row over vertex heights."""
    Minv = plane_coeffs(pts, tet)                          # (a,b) = Minv @ h_tet
    rw = np.array([pts[w,0], pts[w,1], pts[w,2], 1.0])
    # plane_T(r_w) = (a,b)·(rw) = (rw @ Minv) @ h_tet
    coeff = rw @ Minv                                      # length-4, over tet's 4 heights
    row = np.zeros(V)
    for c, vtx in zip(coeff, tet):
        row[vtx] += c
    return row


def slack_face_row(pts, tri, apex, V):
    """slack across interior face = h_apex - plane_{tri+?}(r_apex). Use the tet (tri+apex2)?
       We measure bending as h_apex - (affine through the 3 face verts extended). The 3 face
       verts don't fix an affine in 3D, so use the OTHER tet's plane evaluated at apex."""
    # affine through the face triangle is underdetermined in 3D; instead measure the
    # gap of `apex` above the plane of the tet on the OTHER side (tri + other apex).
    # caller passes the tri and the apex we test; we need the other apex -> handled outside.
    raise NotImplementedError


def build(pts, tets, inter):
    V = len(pts)
    # global convexity rows: for each tet T and vertex w not in T:  h_w - plane_T(r_w) >= 0
    conv_rows = []
    for t in tets:
        tset = set(t)
        for w in range(V):
            if w in tset:
                continue
            row = np.zeros(V); row[w] += 1.0
            row -= plane_value_row(pts, t, w, V)
            conv_rows.append(row)
    conv_rows = np.array(conv_rows)                          # (Ncon, V), each must be >=0
    # bending slacks per interior face: gap of one apex above the other tet's plane
    slack_rows = []
    for (tri, ap1, ap2) in inter:
        tetA = tuple(tri) + (ap1,)                           # tet on side A
        row = np.zeros(V); row[ap2] += 1.0
        row -= plane_value_row(pts, tetA, ap2, V)            # h_ap2 - plane_A(r_ap2)
        slack_rows.append(row)
    slack_rows = np.array(slack_rows)                        # (E, V)
    return conv_rows, slack_rows


def affine_residual(pts, delta):
    A = np.column_stack([np.ones(len(pts)), pts])
    coef, *_ = np.linalg.lstsq(A, delta, rcond=None)
    return np.linalg.norm(delta - A @ coef)


def reduced_dc(conv, slack, h, tie=None):
    V = conv.shape[1]
    # variable Q (length V). P = Q + h.
    # Q convex:  conv @ Q >= 0
    # P convex:  conv @ (Q+h) >= 0  ->  conv @ Q >= -conv@h
    cf = conv @ h
    A_ub = np.vstack([-conv, -conv])
    b_ub = np.concatenate([np.zeros(conv.shape[0]), cf])      # conv@Q>=0 ; conv@Q>=-cf
    c = slack.sum(axis=0).astype(float)
    if tie is not None:
        c = c + tie
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=[(None, None)]*V, method="highs")
    return res


def analyze(name, pts, tets, inter, conv, slack, h):
    res0 = reduced_dc(conv, slack, h)
    if not res0.success:
        print(f"\n=== {name}: LP status {res0.message} ==="); return None
    obj = float(slack.sum(0) @ res0.x)
    lam = slack @ h
    print(f"\n=== {name}  (V={len(pts)}, tets={len(tets)}, interior faces={len(inter)}) ===")
    print(f"    f curvature: {(lam>1e-9).sum()} convex, {(lam<-1e-9).sum()} concave faces")
    print(f"    min total bending Σ slack(Q) = {obj:.6f}")
    rng = np.random.default_rng(0)
    eps = 1e-4 * (abs(obj) + 1)
    sols = []
    for s in range(8):
        tie = eps * (rng.standard_normal(slack.shape[0]) @ slack)
        r = reduced_dc(conv, slack, h, tie=tie)
        if r.success and float(slack.sum(0) @ r.x) <= obj + 80*eps:
            sols.append(r.x)
    worst, pair = 0.0, None
    for i in range(len(sols)):
        for j in range(i+1, len(sols)):
            d = affine_residual(pts, sols[i]-sols[j])
            if d > worst: worst, pair = d, (sols[i], sols[j])
    uniq = worst < 1e-6
    print(f"    optimal-Q non-affine spread over tie-breaks = {worst:.3e}  "
          f"-> {'UNIQUE (mod affine)' if uniq else 'NON-UNIQUE -> 3D COUNTEREXAMPLE'}")
    return None if uniq else (pts, conv, slack, h, obj, pair)


# ---------------- run ----------------
pts, tets, inter = build_mesh(3, 3, 3)
conv, slack = build(pts, tets, inter)
ctr = pts.mean(0)
R = (pts - ctr)
X, Y, Z = R[:,0], R[:,1], R[:,2]

cases = {
    "convex bowl x²+y²+z² (control)": X**2 + Y**2 + Z**2,
    "saddle x²+y²-2z²":               X**2 + Y**2 - 2*Z**2,
    "saddle x²-y²":                   X**2 - Y**2,
    "octahedral |x|+|y|-|z|":         np.abs(X)+np.abs(Y)-np.abs(Z),
    "|x|-|y| (sparse, free faces)":   np.abs(X)-np.abs(Y),
    "monkey-ish x³-3xy² (+0 z)":      X**3 - 3*X*Y**2,
    "triple saddle xyz":              X*Y*Z,
}

found = None
for name, h in cases.items():
    out = analyze(name, pts, tets, inter, conv, slack, np.asarray(h, float))
    if out is not None and found is None:
        found = (name, out)

print("\n" + "=" * 64)
if found:
    name, (pts, conv, slack, h, obj, (Q1, Q2)) = found
    print(f"3D COUNTEREXAMPLE on: {name}")
    print("=" * 64)
    for tag, Q in [("Q1", Q1), ("Q2", Q2)]:
        P = Q + h
        cQ = (conv @ Q).min(); cP = (conv @ P).min()
        print(f"  {tag}: Q convex={cQ>=-1e-6}  P=Q+f convex={cP>=-1e-6}  "
              f"P-Q==f={np.allclose(P-Q,h,atol=1e-9)}  bending={(slack@Q).sum():.6f}")
    print(f"  Q1,Q2 differ by NON-affine function: residual={affine_residual(pts,Q1-Q2):.4e}")
    print("  => reduced-DC uniqueness FAILS in 3D.  Threshold is dimension 3.")
else:
    print("No 3D counterexample in this battery — reduced DC appeared UNIQUE (mod affine).")
    print("Evidence the 1D theorem lifts through 3D; candidate: unique in all dimensions.")
