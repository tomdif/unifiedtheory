"""Does the bare causal order of a sprinkled causal set see a hole?

Companion to UnifiedTheory/Audit/KFCausalAharonovBohm.lean.  A flat U(1)
cocycle on ALL relations of a causal set is classified by H^1 of its order
complex (chains = simplices).  The Lean file proves it is trivial on directed
orders and non-trivial on the crown; this script measures b0, b1 of the order
complex for Poisson sprinklings of

  cyl  : 1+1 cylinder S^1(L=1) x [0,T]         (pi_1 = Z, globally hyperbolic)
  hole : 2+1 Minkowski, disc window R minus a world-tube of radius r0,
         slab [0,T]; causal relation = shortest spatial path around the tube
  flat : the same 2+1 window with no tube (control)

Homotopy type is preserved by removing beat points (Stong), so we reduce to
the core and then take GF(2) ranks of the boundary maps on the core's order
complex up to dimension 2.

Usage: python3.11 scripts/ab_order_complex_h1.py
"""
import numpy as np
import sys

rng = np.random.default_rng(0)


def relation_cyl(P):
    t, x = P[:, 0], P[:, 1]
    dt = t[None, :] - t[:, None]
    dx = np.abs(x[None, :] - x[:, None]) % 1.0
    dx = np.minimum(dx, 1.0 - dx)
    return dt > dx  # R[i,j]: i < j


def around_disc(p, q, r0):
    """Shortest planar path length from p to q avoiding the open disc |z|<r0."""
    d = q - p
    L = np.linalg.norm(d)
    if L == 0:
        return 0.0
    s = np.clip(-np.dot(p, d) / (L * L), 0.0, 1.0)
    if np.linalg.norm(p + s * d) >= r0:
        return L
    a, b = np.linalg.norm(p), np.linalg.norm(q)
    ta, tb = np.sqrt(max(a * a - r0 * r0, 0)), np.sqrt(max(b * b - r0 * r0, 0))
    ang = np.arccos(np.clip(np.dot(p, q) / (a * b), -1, 1))
    arc = ang - np.arccos(min(r0 / a, 1)) - np.arccos(min(r0 / b, 1))
    return ta + tb + r0 * max(arc, 0.0)


def relation_plane(P, r0):
    n = len(P)
    t, X = P[:, 0], P[:, 1:]
    R = np.zeros((n, n), bool)
    for i in range(n):
        for j in range(n):
            dt = t[j] - t[i]
            if dt <= 0:
                continue
            dist = np.linalg.norm(X[j] - X[i]) if r0 == 0 else around_disc(X[i], X[j], r0)
            R[i, j] = dt > dist
    return R


def core(R):
    """Remove beat points until none remain (homotopy-preserving)."""
    alive = np.ones(len(R), bool)
    changed = True
    while changed:
        changed = False
        for x in np.flatnonzero(alive):
            for down, side in ((True, R[:, x]), (False, R[x, :])):  # below / above
                S = np.flatnonzero(side & alive)
                if len(S) == 0:
                    continue
                # down beat: the set below x has a maximum m (everything in S is <= m)
                sub = R[np.ix_(S, S)]
                if down:
                    tops = [k for k in range(len(S)) if sub[:, k].sum() == len(S) - 1]
                else:
                    tops = [k for k in range(len(S)) if sub[k, :].sum() == len(S) - 1]
                if tops:
                    alive[x] = False
                    changed = True
                    break
    idx = np.flatnonzero(alive)
    return R[np.ix_(idx, idx)]


def gf2_rank(rows):
    basis = {}
    r = 0
    for v in rows:
        while v:
            h = v.bit_length() - 1
            if h in basis:
                v ^= basis[h]
            else:
                basis[h] = v
                r += 1
                break
    return r


def betti01(R, max_tri=3_000_000):
    n = len(R)
    edges = [(i, j) for i in range(n) for j in range(n) if R[i, j]]
    eid = {e: k for k, e in enumerate(edges)}
    d1 = [(1 << i) | (1 << j) for i, j in edges]
    r1 = gf2_rank(d1)
    tris = []
    for i, j in edges:
        for k in np.flatnonzero(R[j]):
            tris.append((1 << eid[(i, j)]) | (1 << eid[(j, int(k))]) | (1 << eid[(i, int(k))]))
            if len(tris) > max_tri:
                return None
    r2 = gf2_rank(tris)
    return n - r1, len(edges) - r1 - r2


def sprinkle(kind, T, rho, R0=1.0, r0=0.3):
    if kind == "cyl":
        n = rng.poisson(rho * T)
        P = np.c_[rng.uniform(0, T, n), rng.uniform(0, 1, n)]
        return relation_cyl(P)
    area = np.pi * (R0**2 - (r0 if kind == "hole" else 0) ** 2)
    n = rng.poisson(rho * area * T)
    pts = []
    while len(pts) < n:
        z = rng.uniform(-R0, R0, 2)
        rr = np.linalg.norm(z)
        if rr < R0 and (kind != "hole" or rr > r0):
            pts.append(z)
    P = np.c_[rng.uniform(0, T, n), np.array(pts).reshape(-1, 2)]
    return relation_plane(P, r0 if kind == "hole" else 0)


def main():
    runs = [("cyl", rho, T) for rho in (300,) for T in (0.1, 0.2, 0.35, 0.5, 0.75, 1.0)]
    runs += [(k, 120, T) for k in ("hole", "flat") for T in (0.3, 0.6, 1.0, 1.5, 2.5)]
    seeds = 4
    print(f"{'kind':5} {'rho':>4} {'T':>5}  N(mean)  core  b0,b1 per seed")
    for kind, rho, T in runs:
        res, Ns, cs = [], [], []
        for _ in range(seeds):
            R = sprinkle(kind, T, rho)
            Ns.append(len(R))
            C = core(R)
            cs.append(len(C))
            res.append(betti01(C))
        print(f"{kind:5} {rho:>4} {T:>5}  {np.mean(Ns):7.0f}  {np.mean(cs):4.0f}  {res}")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
