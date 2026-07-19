#!/usr/bin/env python3
r"""
verify_hyperplane_class.py

Check whether each 3D-battery test case is a HYPERPLANE FUNCTION (= one-hidden-layer
ReLU net), which Brandenburg-Grillo-Hertlich Ex. 4.18 proves has a UNIQUE minimal
decomposition. If so, that "test" was re-confirming a theorem, not probing the open
question.

A hyperplane function is f = Σ_i λ_i max{affine, affine}. A SEPARABLE function
f(r) = Σ_axis (±) φ(coord) with each single-coordinate part convex PL is a hyperplane
function: each 1D convex PL part = Σ c_k |coord − t_k| = Σ c_k max{2 affines}.

For each case we propose the natural axis-separable g − h and TEST it on the mesh:
g, h convex (conv·g ≥ 0, conv·h ≥ 0) and g − h = f. If valid ⇒ hyperplane function
⇒ proven unique (Ex. 4.18).  Non-separable cases (xyz, monkey) admit no such split.
"""
import itertools
import numpy as np
np.set_printoptions(suppress=True, precision=4)


def build_mesh(n):
    verts = [(i, j, k) for k in range(n) for j in range(n) for i in range(n)]
    idx = {v: t for t, v in enumerate(verts)}
    e = [np.array(v) for v in [(1,0,0),(0,1,0),(0,0,1)]]
    tets = []
    for k in range(n-1):
        for j in range(n-1):
            for i in range(n-1):
                base = np.array((i, j, k))
                for perm in itertools.permutations(range(3)):
                    cur = base.copy(); path = [cur.copy()]
                    for d in perm:
                        cur = cur + e[d]; path.append(cur.copy())
                    tets.append(tuple(idx[tuple(p)] for p in path))
    return np.array(verts, float), tets, idx


def plane_value_row(pts, tet, w, V):
    M = np.column_stack([pts[list(tet)], np.ones(4)])
    rw = np.array([pts[w,0], pts[w,1], pts[w,2], 1.0])
    coeff = rw @ np.linalg.inv(M)
    row = np.zeros(V)
    for c, vtx in zip(coeff, tet):
        row[vtx] += c
    return row


def convex_rows(pts, tets):
    V = len(pts)
    rows = []
    for t in tets:
        ts = set(t)
        for w in range(V):
            if w in ts: continue
            r = np.zeros(V); r[w] += 1.0; r -= plane_value_row(pts, t, w, V)
            rows.append(r)
    return np.array(rows)


pts, tets, idx = build_mesh(3)
conv = convex_rows(pts, tets)
V = len(pts)
ctr = pts.mean(0); R = pts - ctr
X, Y, Z = R[:,0], R[:,1], R[:,2]
TOL = 1e-9


def is_convex(g):
    return (conv @ g).min() >= -TOL


# (name, f, g, h) with axis-separable g,h; None g,h = no separable split
cases = [
    ("x²+y²+z² (convex control)", X**2+Y**2+Z**2, X**2+Y**2+Z**2, np.zeros(V)),
    ("x²+y²-2z²",                 X**2+Y**2-2*Z**2, X**2+Y**2, 2*Z**2),
    ("x²-y²",                     X**2-Y**2, X**2, Y**2),
    ("octahedral |x|+|y|-|z|",    np.abs(X)+np.abs(Y)-np.abs(Z), np.abs(X)+np.abs(Y), np.abs(Z)),
    ("|x|-|y|",                   np.abs(X)-np.abs(Y), np.abs(X), np.abs(Y)),
    ("monkey x³-3xy²",            X**3-3*X*Y**2, None, None),
    ("triple saddle xyz",         X*Y*Z, None, None),
]

print(f"3D mesh: V={V}, tets={len(tets)}, convexity rows={conv.shape[0]}\n")
print(f"{'case':<28} {'axis-separable g-h valid?':<26} {'class'}")
print("-"*78)
results = {}
for name, f, g, h in cases:
    if g is None:
        verdict = "no separable split"
        cls = "OUTSIDE Ex.4.18 (genuine probe)"
        ok = False
    else:
        gc, hc = is_convex(g), is_convex(h)
        diff = np.allclose(g - h, f, atol=TOL)
        ok = gc and hc and diff
        verdict = f"g cvx={gc} h cvx={hc} g-h=f={diff}"
        cls = "HYPERPLANE FN -> PROVEN UNIQUE (Ex.4.18)" if ok else "separable split FAILED"
    results[name] = ok
    print(f"{name:<28} {verdict:<26} {cls}")

n_proven = sum(results.values())
print("\n" + "="*78)
print(f"SUMMARY: {n_proven}/{len(cases)} cases are hyperplane functions = "
      f"PROVEN UNIQUE (Brandenburg-Grillo-Hertlich Ex. 4.18).")
print(f"         {len(cases)-n_proven}/{len(cases)} sit outside the named proven-unique "
      f"classes: monkey x³-3xy², xyz.")
print("""
These two are the ONLY genuine probes of the open question — and (a) both are highly
symmetric (decomposition polyhedron likely single-vertex by symmetry), and (b) my
detector is unreliable (dual-support certificate overcounts; tie-break only generic),
so I cannot currently certify even their 'unique' verdicts.

CONCLUSION: the 3D battery is ~5/7 theorem-confirmations (separable quadratics + abs
functions are all one-hidden-layer ReLU nets) and ~2/7 untrustworthy symmetric probes.
It contains essentially NO clean evidence for the universal conjecture.
""")
