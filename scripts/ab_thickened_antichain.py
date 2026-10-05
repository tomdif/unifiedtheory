"""Mesoscale test: does the thickened-antichain nerve see the hole, and carry its flux?

Follow-up to ab_order_complex_h1.py (global order complex: b1 never isolates the
hole).  Here we use the Major–Rideout–Surya construction (gr-qc/0604124):

  A        : an inextendible-ish antichain = minimal elements of {t >= t0}
  T_n(A)   : { x in J+(A) : |J-(x) \\ J-(A)| <= n }      (thickened antichain)
  shadows  : for each maximal m of T_n(A), P(m) = J-(m) ∩ A
  nerve    : simplices = sets of maximal elements with a common shadow element

and measure b0, b1 of the nerve vs the thickening n.  Targets:

  cyl  : 1+1 cylinder S^1(L=1); slice is a circle      -> expect b1 = 1
  hole : 2+1 disc R0=1 minus world-tube r0=0.3          -> annulus, b1 = 1
  flat : 2+1 disc R0=1, no tube (control)               -> disc,    b1 = 0

Flux: on the nerve put the AB cochain U(m,m') = exp(i Φ Δθ(m,m')/2π), with
Δθ the wrapped angle difference of shadow centroids about the hole.  It is
flat on a triangle iff the triangle has zero winding; we count non-flat
triangles and report the winding (hence holonomy e^{iΦ·w}) of a generating
cycle of H1.

Usage: python3.11 scripts/ab_thickened_antichain.py
"""
import numpy as np
import sys
from ab_order_complex_h1 import gf2_rank

rng = np.random.default_rng(1)


# ---------------------------------------------------------------- sprinklings
def sprinkle_cyl(rho, T):
    n = rng.poisson(rho * T)
    t, x = rng.uniform(0, T, n), rng.uniform(0, 1, n)
    dx = np.abs(x[None, :] - x[:, None]) % 1.0
    dx = np.minimum(dx, 1.0 - dx)
    R = (t[None, :] - t[:, None]) > dx
    ang = 2 * np.pi * x
    return t, ang, R


def around_disc_row(p, Q, r0):
    """Shortest planar path lengths from p to each row of Q avoiding |z|<r0."""
    D = Q - p
    L2 = np.einsum("ij,ij->i", D, D)
    L = np.sqrt(L2)
    s = np.clip(-(D @ p) / np.where(L2 > 0, L2, 1), 0, 1)
    closest = np.linalg.norm(p + s[:, None] * D, axis=1)
    a = np.linalg.norm(p)
    b = np.linalg.norm(Q, axis=1)
    ta = np.sqrt(max(a * a - r0 * r0, 0))
    tb = np.sqrt(np.maximum(b * b - r0 * r0, 0))
    ang = np.arccos(np.clip((Q @ p) / (a * b), -1, 1))
    arc = ang - np.arccos(min(r0 / a, 1)) - np.arccos(np.minimum(r0 / b, 1))
    around = ta + tb + r0 * np.maximum(arc, 0)
    return np.where(closest >= r0, L, around)


def sprinkle_plane(rho, T, hole, R0=1.0, r0=0.3):
    rin = r0 if hole else 0.0
    n = rng.poisson(rho * np.pi * (R0**2 - rin**2) * T)
    r = np.sqrt(rng.uniform(rin**2, R0**2, n))
    ang = rng.uniform(0, 2 * np.pi, n)
    X = np.c_[r * np.cos(ang), r * np.sin(ang)]
    t = rng.uniform(0, T, n)
    R = np.zeros((n, n), bool)
    for i in range(n):
        dist = around_disc_row(X[i], X, r0) if hole else np.linalg.norm(X - X[i], axis=1)
        R[i] = (t - t[i]) > dist
    return t, ang, R


# ------------------------------------------------------------ thickened nerve
def antichain(t, R, t0):
    up = np.flatnonzero(t >= t0)
    sub = R[np.ix_(up, up)]
    return up[~sub.any(axis=0)]  # minimal elements of {t >= t0}


def nerve_betti(t, ang, R, A, ns, Phi=1.0):
    N = len(t)
    inA = np.zeros(N, bool)
    inA[A] = True
    # J-(A): elements y with y <= a for some a in A
    pastA = inA | R[:, A].any(axis=1)
    futA = inA | R[A, :].any(axis=0)
    # |J-(x) \ J-(A)| for x in J+(A): count y not in J-(A) with y < x, plus x itself
    outside = ~pastA
    cnt = (R[outside, :].sum(axis=0)) + outside.astype(int)
    Aidx = {a: k for k, a in enumerate(A)}
    out = []
    for n in ns:
        Tn = np.flatnonzero(futA & (cnt <= n))
        sub = R[np.ix_(Tn, Tn)]
        M = Tn[~sub.any(axis=1)]  # maximal elements of T_n
        shadows = []
        for m in M:
            s = np.array([m]) if inA[m] else A[R[A, m]]
            bits = 0
            for a in s:
                bits |= 1 << Aidx[a]
            shadows.append((bits, s))
        # drop shadows contained in another (same nerve homotopy type, smaller)
        keep = []
        order = sorted(range(len(shadows)), key=lambda k: -bin(shadows[k][0]).count("1"))
        for k in order:
            b = shadows[k][0]
            if b and not any((b | shadows[j][0]) == shadows[j][0] for j in keep):
                keep.append(k)
        V = [shadows[k] for k in keep]
        nv = len(V)
        edges = [(i, j) for i in range(nv) for j in range(i + 1, nv) if V[i][0] & V[j][0]]
        eid = {e: k for k, e in enumerate(edges)}
        nbr = [set() for _ in range(nv)]
        for i, j in edges:
            nbr[i].add(j)
        tris = []
        for i, j in edges:
            for k in nbr[j]:
                if k in nbr[i] and V[i][0] & V[j][0] & V[k][0]:
                    tris.append((i, j, k))
        r1 = gf2_rank([(1 << i) | (1 << j) for i, j in edges])
        r2 = gf2_rank([(1 << eid[(i, j)]) | (1 << eid[(j, k)]) | (1 << eid[(i, k)]) for i, j, k in tris])
        b0, b1 = nv - r1, len(edges) - r1 - r2
        # AB cochain: centroid angle of each shadow, wrapped differences
        cen = np.array([np.angle(np.exp(1j * ang[s]).mean()) for _, s in V])
        dth = lambda i, j: np.angle(np.exp(1j * (cen[j] - cen[i])))
        nonflat = sum(1 for i, j, k in tris
                      if abs(dth(i, j) + dth(j, k) - dth(i, k)) > 1e-9)
        out.append((n, len(A), len(M), nv, b0, b1, len(tris), nonflat,
                    generator_winding(nv, edges, dth) if b1 >= 1 else None))
    return out


def generator_winding(nv, edges, dth):
    """Winding of the fundamental cycles of a BFS spanning tree, max |w|."""
    adj = [[] for _ in range(nv)]
    for i, j in edges:
        adj[i].append(j)
        adj[j].append(i)
    phase = [None] * nv
    ws = []
    for root in range(nv):
        if phase[root] is not None:
            continue
        phase[root] = 0.0
        q = [root]
        while q:
            u = q.pop()
            for v in adj[u]:
                if phase[v] is None:
                    phase[v] = phase[u] + dth(u, v)
                    q.append(v)
    for i, j in edges:
        ws.append(round((phase[i] + dth(i, j) - phase[j]) / (2 * np.pi)))
    return max(ws, key=abs)


def report(name, t, ang, R, t0, ns):
    A = antichain(t, R, t0)
    print(f"--- {name}: N={len(t)}, |A|={len(A)}")
    print("   n  |max|  nerveV  b0  b1  tris  nonflat  max-winding")
    for n, a, m, nv, b0, b1, nt, nf, w in nerve_betti(t, ang, R, A, ns):
        print(f"{n:4d}  {m:5d}  {nv:6d}  {b0:2d}  {b1:2d}  {nt:5d}  {nf:7d}  {w}")
    sys.stdout.flush()


def main():
    ns = [0, 1, 2, 3, 5, 8, 12, 18, 25, 35, 50, 70, 100, 140, 200]
    for rho in (1000, 3000):
        t, ang, R = sprinkle_cyl(rho, 1.0)
        report(f"cyl rho={rho}", t, ang, R, 0.3, ns)
    for hole in (True, False):
        t, ang, R = sprinkle_plane(1500, 0.7, hole)
        report(f"{'hole' if hole else 'flat'} rho=1500", t, ang, R, 0.2, ns)


if __name__ == "__main__":
    main()
