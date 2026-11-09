"""Dirac monopole on a causal set: b2 of the thickened-antichain nerve on R x S^2,
and lattice Chern numbers of a monopole connection on that nerve.

Follow-up to ab_thickened_antichain.py (b1 / AB holonomy on the cylinder).

(a) Sprinkle into 2+1 R x S^2(radius rs) and R x D^2 (control, same area).
    Thickened antichain T_n(A) -> maximal elements -> shadows on A -> nerve
    (simplices = sets of shadows with a common element of A).  Betti numbers
    b0, b1, b2 over GF(2) (needs 3-simplices for rank d3).  All ORDER-ONLY.

(b) In the b2 = 1 window: vertex position = normalized centroid of its shadow
    (EMBEDDING-DEPENDENT).  Link phase of a charge-g monopole in Dirac-string
    gauge A = (g/2)(1 - cos th) dphi (string through the south pole):
        theta_uv = (g/2) * Omega(N, u, v)       (exact geodesic line integral)
    with Omega the signed solid angle (Van Oosterom-Strackee).  Plaquette
    F_tau = principal value of the oriented edge sum; integer m_tau = (F - raw)/2pi.
    Checks:  delta m = 0 on every 3-simplex (no 'monopole inside a tetrahedron');
    Chern number c = <F, z>/2pi on a real 2-cycle z normalised by <Omega, z> = 4pi
    (z = projection of the solid-angle cochain onto ker d2; boundaries pair to 0).
    For non-integer g the string becomes visible: some plaquettes carry
    |F - (g/2)Omega| = 2pi*frac(g) and c is still an integer (Dirac quantization).

Usage: OMP_NUM_THREADS=1 nice -n 10 python3.11 scripts/ab_monopole_nerve.py [seed]
"""
import sys
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.linalg import lsqr

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from ab_order_complex_h1 import gf2_rank

SEED = int(sys.argv[1]) if len(sys.argv) > 1 else 1
rng = np.random.default_rng(SEED)


# ---------------------------------------------------------------- sprinklings
def sprinkle_sphere(rho, T, rs):
    n = rng.poisson(rho * 4 * np.pi * rs**2 * T)
    X = rng.normal(size=(n, 3))
    X /= np.linalg.norm(X, axis=1)[:, None]
    t = rng.uniform(0, T, n)
    d = rs * np.arccos(np.clip(X @ X.T, -1, 1))
    R = (t[None, :] - t[:, None]) > d
    return t, X, R


def sprinkle_disc(rho, T, rd):
    n = rng.poisson(rho * np.pi * rd**2 * T)
    r = rd * np.sqrt(rng.uniform(0, 1, n))
    a = rng.uniform(0, 2 * np.pi, n)
    P = np.c_[r * np.cos(a), r * np.sin(a)]
    t = rng.uniform(0, T, n)
    d = np.linalg.norm(P[:, None, :] - P[None, :, :], axis=2)
    R = (t[None, :] - t[:, None]) > d
    # embed disc on the northern cap of the unit sphere (only used for phases)
    th = r / rd * (np.pi / 2)
    X = np.c_[np.sin(th) * np.cos(a), np.sin(th) * np.sin(a), np.cos(th)]
    return t, X, R


# ------------------------------------------------------------ thickened nerve
def antichain(t, R, t0):
    up = np.flatnonzero(t >= t0)
    sub = R[np.ix_(up, up)]
    return up[~sub.any(axis=0)]


def thickening_data(t, R, A):
    N = len(t)
    inA = np.zeros(N, bool)
    inA[A] = True
    pastA = inA | R[:, A].any(axis=1)
    futA = inA | R[A, :].any(axis=0)
    outside = ~pastA
    cnt = R[outside, :].sum(axis=0) + outside.astype(int)
    return inA, futA, cnt


def nerve(R, A, inA, futA, cnt, n, max_tet=400_000):
    Aidx = {a: k for k, a in enumerate(A)}
    Tn = np.flatnonzero(futA & (cnt <= n))
    sub = R[np.ix_(Tn, Tn)]
    M = Tn[~sub.any(axis=1)]
    sh = []
    for m in M:
        s = np.array([m]) if inA[m] else A[R[A, m]]
        bits = 0
        for a in s:
            bits |= 1 << Aidx[a]
        sh.append((bits, s))
    keep = []
    for k in sorted(range(len(sh)), key=lambda k: -bin(sh[k][0]).count("1")):
        b = sh[k][0]
        if b and not any((b | sh[j][0]) == sh[j][0] for j in keep):
            keep.append(k)
    V = [sh[k] for k in keep]
    nv = len(V)
    B = [v[0] for v in V]
    nbr = [set() for _ in range(nv)]
    edges = []
    for i in range(nv):
        for j in range(i + 1, nv):
            if B[i] & B[j]:
                edges.append((i, j))
                nbr[i].add(j)
    tris = []
    for i, j in edges:
        bij = B[i] & B[j]
        for k in nbr[j]:
            if k in nbr[i] and bij & B[k]:
                tris.append((i, j, k))
    tets = []
    for i, j, k in tris:
        bijk = B[i] & B[j] & B[k]
        for l in nbr[k]:
            if l in nbr[i] and l in nbr[j] and bijk & B[l]:
                tets.append((i, j, k, l))
                if len(tets) > max_tet:
                    return V, edges, tris, None
    return V, edges, tris, tets


def betti(nv, edges, tris, tets):
    eid = {e: k for k, e in enumerate(edges)}
    tid = {t: k for k, t in enumerate(tris)}
    r1 = gf2_rank([(1 << i) | (1 << j) for i, j in edges])
    r2 = gf2_rank([(1 << eid[(i, j)]) | (1 << eid[(j, k)]) | (1 << eid[(i, k)]) for i, j, k in tris])
    r3 = gf2_rank([(1 << tid[(j, k, l)]) | (1 << tid[(i, k, l)]) | (1 << tid[(i, j, l)]) | (1 << tid[(i, j, k)])
                   for i, j, k, l in tets])
    return nv - r1, len(edges) - r1 - r2, len(tris) - r2 - r3


# ------------------------------------------------------------ monopole / Chern
def solid_angle(a, b, c):
    num = np.einsum("ij,ij->i", a, np.cross(b, c))
    den = 1 + np.einsum("ij,ij->i", a, b) + np.einsum("ij,ij->i", b, c) + np.einsum("ij,ij->i", c, a)
    return 2 * np.arctan2(num, den)


def wrap(x):
    return (x + np.pi) % (2 * np.pi) - np.pi


def chern(X, V, edges, tris, tets, gs):
    P = np.array([X[s].mean(axis=0) for _, s in V])
    P /= np.linalg.norm(P, axis=1)[:, None]
    Np = np.tile([0.0, 0.0, 1.0], (len(edges), 1))
    e = np.array(edges)
    tr = np.array(tris)
    omN = solid_angle(Np, P[e[:, 0]], P[e[:, 1]])           # Omega(N,u,v) per edge
    eid = {ed: k for k, ed in enumerate(edges)}
    ij = np.array([eid[(i, j)] for i, j, k in tris])
    jk = np.array([eid[(j, k)] for i, j, k in tris])
    ik = np.array([eid[(i, k)] for i, j, k in tris])
    Om = solid_angle(P[tr[:, 0]], P[tr[:, 1]], P[tr[:, 2]])  # oriented triangle solid angle
    # real 2-cycle z: project Omega onto ker d2  (z = Om - d2^T y)
    rows = np.repeat(np.arange(len(tris)), 3)
    cols = np.c_[jk, ik, ij].ravel()
    vals = np.tile([1.0, -1.0, 1.0], len(tris))            # d(ijk) = jk - ik + ij
    D2 = csr_matrix((vals, (rows, cols)), shape=(len(tris), len(edges))).T  # edges x tris
    y = lsqr(D2.T, Om, atol=1e-12, btol=1e-12, iter_lim=20000)[0]
    z = Om - D2.T @ y
    resid = np.abs(D2 @ z).max()
    norm = Om @ z
    print(f"  [diag] <Omega,z_proj>/(4pi) before normalisation = {norm/(4*np.pi):.4f}, |z|={np.linalg.norm(z):.3f}")
    if abs(norm) < 1e-6 * max(1.0, np.linalg.norm(Om)) ** 2:
        return None
    z *= 4 * np.pi / norm                                     # <Omega, z> = 4pi
    tid = {t: k for k, t in enumerate(tris)}
    out = []
    for g in gs:
        th = (g / 2) * omN
        raw = th[ij] + th[jk] - th[ik]
        F = wrap(raw)
        m = np.rint((F - raw) / (2 * np.pi)).astype(int)
        # delta m on 3-simplices (ijkl): faces jkl - ikl + ijl - ijk
        dm = 0
        if tets:
            T4 = np.array(tets)
            f = lambda a, b, c: np.array([tid[(x, y_, w)] for x, y_, w in zip(a, b, c)])
            jkl = f(T4[:, 1], T4[:, 2], T4[:, 3]); ikl = f(T4[:, 0], T4[:, 2], T4[:, 3])
            ijl = f(T4[:, 0], T4[:, 1], T4[:, 3]); ijk = f(T4[:, 0], T4[:, 1], T4[:, 2])
            dm = int(np.count_nonzero(m[jkl] - m[ikl] + m[ijl] - m[ijk]))
        c = F @ z / (2 * np.pi)
        string = int(np.count_nonzero(np.abs(wrap(F - (g / 2) * Om)) > 1e-6))
        out.append((g, c, dm, string, np.abs(F).max()))
    return resid, out


# ------------------------------------------------------------------- driver
def scan(name, t, X, R, t0, ns, gs, do_chern=True):
    A = antichain(t, R, t0)
    inA, futA, cnt = thickening_data(t, R, A)
    print(f"--- {name}: N={len(t)}, |A|={len(A)}   (seed {SEED})")
    print("    n  nerveV  edges   tris    tets   b0 b1 b2")
    rows = []
    for n in ns:
        V, edges, tris, tets = nerve(R, A, inA, futA, cnt, n)
        if tets is None:
            print(f"{n:5d}  {len(V):6d} {len(edges):6d} {len(tris):6d}  >cap    (stop)")
            break
        b = betti(len(V), edges, tris, tets)
        print(f"{n:5d}  {len(V):6d} {len(edges):6d} {len(tris):6d} {len(tets):7d}   {b[0]:2d} {b[1]:2d} {b[2]:2d}")
        sys.stdout.flush()
        rows.append((n, b, V, edges, tris, tets))
    if do_chern:
        win = [r for r in rows if r[1] == (1, 0, 1)]
        for n, b, V, edges, tris, tets in win:
            res = chern(X, V, edges, tris, tets, gs)
            if res is None:
                print(f"  n={n}: <Omega,z>~0 -> the 2-cycle does not wrap the sphere (degree 0); no Chern number")
                continue
            resid, out = res
            print(f"  Chern @ n={n}  (|d2 z|max={resid:.1e})")
            print("       g      c=<F,z>/2pi   #tets dm!=0   #string plaquettes   max|F|")
            for g, c, dm, st, mf in out:
                print(f"    {g:5.2f}   {c:12.6f}   {dm:10d}   {st:12d}         {mf:.3f}")
            sys.stdout.flush()
    return rows


def main():
    ns = [1, 2, 3, 5, 8, 12, 18, 25, 35, 50, 70, 100, 140]
    gs = [1, 2, -1, 3, 0.5, 1.3]
    rs = 0.25
    for rho in (2000, 4000):
        t, X, R = sprinkle_sphere(rho, 1.2, rs)
        scan(f"sphere rs={rs} rho={rho}", t, X, R, 0.25, ns, gs)
        del R
    t, X, R = sprinkle_disc(2000, 1.2, 2 * rs)
    scan(f"disc control rd={2*rs} rho=2000", t, X, R, 0.25, ns, gs)
    del R
    t, X, R = sprinkle_disc(4000, 1.2, 2 * rs)
    scan(f"disc control rd={2*rs} rho=4000", t, X, R, 0.25, ns, gs)


if __name__ == "__main__":
    main()
