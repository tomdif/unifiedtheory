"""The AB step on a sprinkled causal set, order-only.

Two chains p < a1 < q and p < a2 < q crossing a slice antichain A on opposite
sides of the hole form the AB diamond.  Their relative phase should be
e^{±iΦ}.  Everything below is computed from the causal order alone; embedding
coordinates are used only for the sprinkling and for a continuum cross-check
of the component counts.

  1. A = minimal elements of {t >= t0}; thicken by n (Major–Rideout–Surya);
     shadows S(m) = J-(m) ∩ A of the maximal elements of T_n(A).
  2. Dowker complex K on A: simplices = subsets of a common shadow
     (homotopy-equivalent to the nerve, Dowker's theorem).  Check b1(K) = 1.
  3. Order-only flat cocycle: in spanning-tree gauge, solve the triangle
     flatness equations over R; the solution space is H^1(K;R).  Scale to the
     integral generator ω (values on fundamental cycles are integers, gcd 1).
     The AB cocycle is Φ·ω; flat U(1) cocycles mod gauge = {Φ} = a circle.
  4. For pairs p < q with p below A and q above, I = J+(p) ∩ J-(q) ∩ A.  The
     chains p < a < q (a ∈ I) fall into classes = components of I in K.
     For two classes, the Wilson factor of chains through a1, a2 is the
     holonomy of the closed curve a1 -> a2 inside J+(p) ∩ A, back inside
     J-(q) ∩ A:  W = exp(iΦ·h), h = ω(loop).  Expect h = ±1, and h = 0 for
     loops inside a single class (control), independent of a1, a2.

Usage: python3.11 scripts/ab_chain_pair_holonomy.py
"""
import numpy as np
from collections import deque, Counter
from ab_thickened_antichain import antichain
from ab_order_complex_h1 import gf2_rank


def sprinkle_cyl(rng, rho, T):
    n = rng.poisson(rho * T)
    t, x = rng.uniform(0, T, n), rng.uniform(0, 1, n)
    dx = np.abs(x[None, :] - x[:, None]) % 1.0
    dx = np.minimum(dx, 1.0 - dx)
    return t, x, (t[None, :] - t[:, None]) > dx


def shadows(R, A, n):
    N = len(R)
    inA = np.zeros(N, bool)
    inA[A] = True
    pastA = inA | R[:, A].any(axis=1)
    futA = inA | R[A, :].any(axis=0)
    out = ~pastA
    cnt = R[out, :].sum(axis=0) + out.astype(int)
    Tn = np.flatnonzero(futA & (cnt <= n))
    M = Tn[~R[np.ix_(Tn, Tn)].any(axis=1)]
    pos = {a: k for k, a in enumerate(A)}
    S = [frozenset([pos[m]]) if inA[m] else frozenset(pos[a] for a in A[R[A, m]]) for m in M]
    S = [s for s in S if s and not any(s < s2 for s2 in S)]
    return list(set(S))


def dowker(nA, S):
    edges, tris = set(), set()
    for s in S:
        v = sorted(s)
        for i in range(len(v)):
            for j in range(i + 1, len(v)):
                edges.add((v[i], v[j]))
                for k in range(j + 1, len(v)):
                    tris.add((v[i], v[j], v[k]))
    edges, tris = sorted(edges), sorted(tris)
    eid = {e: k for k, e in enumerate(edges)}
    r1 = gf2_rank([(1 << i) | (1 << j) for i, j in edges])
    r2 = gf2_rank([(1 << eid[(i, j)]) | (1 << eid[(j, k)]) | (1 << eid[(i, k)]) for i, j, k in tris])
    return edges, tris, eid, nA - r1, len(edges) - r1 - r2


def integral_cocycle(nA, edges, tris, eid):
    adj = [[] for _ in range(nA)]
    for i, j in edges:
        adj[i].append(j)
        adj[j].append(i)
    seen, tree = {0}, set()
    q = deque([0])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if v not in seen:
                seen.add(v)
                tree.add((min(u, v), max(u, v)))
                q.append(v)
    free = [e for e in edges if e not in tree]
    col = {e: k for k, e in enumerate(free)}
    Mx = np.zeros((len(tris), len(free)))
    for r, (i, j, k) in enumerate(tris):
        for e, sgn in (((i, j), 1), ((j, k), 1), ((i, k), -1)):
            if e in col:
                Mx[r, col[e]] += sgn
    _, sv, Vt = np.linalg.svd(Mx) if len(tris) else (None, np.array([]), np.eye(len(free)))
    null = Vt[(sv > 1e-9).sum():]
    assert len(null) == 1, f"H^1 dim {len(null)}"
    w = null[0]
    w = w / np.min(np.abs(w[np.abs(w) > 1e-6]))
    assert np.allclose(w, np.round(w), atol=1e-6), "non-integral cocycle"
    omega = {e: 0.0 for e in tree}
    omega.update({e: float(np.round(w[col[e]])) for e in free})
    return omega, adj


def path(adj, allowed, s, t):
    prev = {s: None}
    q = deque([s])
    while q:
        u = q.popleft()
        if u == t:
            break
        for v in adj[u]:
            if v in allowed and v not in prev:
                prev[v] = u
                q.append(v)
    if t not in prev:
        return None
    p, u = [], t
    while u is not None:
        p.append(u)
        u = prev[u]
    return p[::-1]


def components(adj, nodes):
    nodes, comps = set(nodes), []
    while nodes:
        s = nodes.pop()
        c, q = {s}, [s]
        while q:
            u = q.pop()
            for v in adj[u]:
                if v in nodes:
                    nodes.discard(v)
                    c.add(v)
                    q.append(v)
        comps.append(c)
    return comps


def sub_b1(nodes, edges, tris):
    """b1 (GF(2)) of the Dowker subcomplex induced on a vertex set."""
    E = [e for e in edges if e[0] in nodes and e[1] in nodes]
    Tr = [t for t in tris if t[0] in nodes and t[1] in nodes and t[2] in nodes]
    eid = {e: k for k, e in enumerate(E)}
    r1 = gf2_rank([(1 << i) | (1 << j) for i, j in E])
    r2 = gf2_rank([(1 << eid[(i, j)]) | (1 << eid[(j, k)]) | (1 << eid[(i, k)]) for i, j, k in Tr])
    return len(E) - r1 - r2


def arcs_continuum(xp, wp, xq, wq, xs):
    """Continuum component count of the overlap of two circle arcs, by sampling."""
    d = lambda a, b: np.minimum(np.abs(a - b) % 1, 1 - np.abs(a - b) % 1)
    inside = (d(xs, xp) < wp) & (d(xs, xq) < wq)
    if not inside.any():
        return 0
    k = np.argmin(inside) if not inside.all() else 0
    r = np.roll(inside, -k)
    return 1 if inside.all() else int(np.sum(r[1:] & ~r[:-1]) + r[0])


def run(rho, n, seed, npairs=3000, t0=0.3, T=1.2):
    rng = np.random.default_rng(seed)
    t, x, R = sprinkle_cyl(rng, rho, T)
    A = antichain(t, R, t0)
    S = shadows(R, A, n)
    edges, tris, eid, b0, b1 = dowker(len(A), S)
    print(f"rho={rho} n={n} seed={seed}: N={len(t)} |A|={len(A)} shadows={len(S)} "
          f"Dowker b0={b0} b1={b1}")
    if (b0, b1) != (1, 1):
        return None
    omega, adj = integral_cocycle(len(A), edges, tris, eid)
    hol = lambda loop: sum(omega[(a, b)] if a < b else -omega[(b, a)]
                           for a, b in zip(loop[:-1], loop[1:]))
    below = np.flatnonzero(t < t0 - 0.02)
    above = np.flatnonzero(t > t0 + 0.02)
    xs = np.linspace(0, 1, 4000, endpoint=False)
    stats = Counter()
    agree = Counter()
    for _ in range(npairs):
        p, q = rng.choice(below), rng.choice(above)
        if not R[p, q]:
            continue
        Sp = set(np.flatnonzero(R[p, A]))
        Sq = set(np.flatnonzero(R[A, q]))
        comps = components(adj, Sp & Sq)
        cont = arcs_continuum(x[p], t0 - t[p], x[q], min(t[q] - t0, 0.5001), xs)
        agree[(len(comps), cont)] += 1
        if len(comps) not in (1, 2):
            continue
        hs = set()
        for _ in range(3):  # several representatives a1, a2 and their paths
            c1 = list(comps[0])
            c2 = list(comps[-1])
            a1, a2 = rng.choice(c1), rng.choice(c2)
            if a1 == a2:
                continue
            l1, l2 = path(adj, Sp, a1, a2), path(adj, Sq, a2, a1)
            if l1 is None or l2 is None:
                hs.add("disconnected")
                continue
            hs.add(int(round(hol(l1 + l2[1:]))))
        wraps = sub_b1(Sp, edges, tris) > 0 or sub_b1(Sq, edges, tris) > 0
        key = ("two classes" if len(comps) == 2 else "one class",
               "wrapping J±∩A" if wraps else "contractible J±∩A", tuple(sorted(map(str, hs))))
        stats[key] += 1
    print("  (order-derived #classes, continuum #arcs) counts:", dict(sorted(agree.items())))
    for k, v in sorted(stats.items()):
        print(f"  {k[0]:11s} {k[1]:19s} holonomy values {k[2]}: {v}")


if __name__ == "__main__":
    for rho, n in ((3000, 40), (10000, 120)):
        for seed in (0, 1, 2):
            run(rho, n, seed)
