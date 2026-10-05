"""Z-cover from a circular coordinate (persistent-cohomology style), order only.

Steps (coordinates used only for slice LEVELS, the comparison, and as a
linear extension that any topological sort of the order would replace):
 0. n-window: dim H^1(X) of the slice-stack complex (ab_order_cover) over
    n and seeds; use n where it is 1 for every seed.
 1. Integral cocycle w on X; harmonic representative w + δf by least squares;
    theta = f mod 1 on slice elements (a circle-valued coordinate).
 2. Off-slice elements: theta = circular mean over their past shadow on the
    highest slice below (or future shadow on the lowest slice).
 3. Generators: base LINKS whose slice span <= B, lifted by the nearest rule
    (displacement in [-1/2, 1/2)).  Long links are not lifted.
 4. Transitive closure on sheets; compare with the coordinate cover entry by
    entry (gauge-matched on the generators), FN by proper time; image counts.
 5. End to end: Johnston K on the order-built cover, K_Phi = sum_j e^{ijPhi}
    K_cover((u,0),(v,j)), vs continuum sum_k e^{ikPhi} 1/2 J0(m tau_k).

Usage: python3.11 scripts/ab_circular_cover.py [scan|cover|e2e]
"""
import sys
import numpy as np
from collections import deque, Counter, defaultdict
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import lsqr
from scipy.linalg import solve_triangular
from scipy.special import j0
import ab_order_cover as oc


def complex_cocycle(seed, rho, n, T=1.4):
    t, x, R, V, sl, edges, inter = oc.build(seed, rho, T=T, n=n)
    cells, nbr = oc.cells_of(edges, inter, sl)
    val, nfree, rank, _, conn, Cm = oc.cocycle(len(V), edges, cells, nbr)
    return t, x, R, V, sl, edges, inter, val, nfree - rank, nfree, Cm


def scan(seeds=range(5), ns=(15, 20, 25, 35, 50, 70), rho=3000):
    print(f"n-window scan, rho={rho}: dim H^1(X) per seed")
    for n in ns:
        dims = []
        for sd in seeds:
            *_, h1, nfree, Cm = complex_cocycle(sd, rho, n)
            dims.append(h1)
        print(f"  n={n:3d}: {dims}", flush=True)


def harmonic_theta(V, edges, val, nfree, Cm):
    if nfree == 1:
        g = np.array([1, 1])
    else:
        _, sv, Vt = np.linalg.svd(Cm[:, 1:].astype(float))
        gg = Vt[-1] / np.min(np.abs(Vt[-1][np.abs(Vt[-1]) > 1e-6]))
        g = np.concatenate([[1], np.round(gg).astype(int)])
    w = np.array([np.pad(val[e], (0, 1 + nfree - len(val[e]))) @ g for e in edges], float)
    E = len(edges)
    rows = np.repeat(np.arange(E), 2)
    cols = np.array(edges).ravel()
    data = np.tile([-1.0, 1.0], E)  # (D f)_e = f_j - f_i
    D = coo_matrix((data, (rows, cols)), shape=(E, len(V))).tocsr()
    f = lsqr(D, -w, atol=1e-12, btol=1e-12, iter_lim=20000)[0]
    resid = w + D @ f  # harmonic cocycle values
    return np.mod(f, 1.0), resid


def circ_mean(th):
    return np.mod(np.angle(np.exp(2j * np.pi * th).mean()) / (2 * np.pi), 1.0)


def all_theta(R, V, sl, theta_V):
    N = len(R)
    theta = np.full(N, np.nan)
    sidx = np.full(N, -1)
    theta[V] = theta_V
    sidx[V] = sl
    nsl = sl.max() + 1
    members = [V[sl == s] for s in range(nsl)]
    thm = [theta_V[sl == s] for s in range(nsl)]
    for y in range(N):
        if not np.isnan(theta[y]):
            continue
        for s in range(nsl - 1, -1, -1):  # highest slice with elements in J-(y)
            m = R[members[s], y]
            if m.any():
                theta[y], sidx[y] = circ_mean(thm[s][m]), s
                break
        else:
            m = R[y, members[0]]
            if m.any():
                theta[y], sidx[y] = circ_mean(thm[0][m]), 0
    return theta, sidx


def lift(seed, rho, n, B=5, S=3, T=1.4, quiet=False, dmax=None):
    t, x, R, V, sl, edges, inter, val, h1, nfree, Cm = complex_cocycle(seed, rho, n, T)
    if h1 != 1:
        print(f"seed={seed}: dim H^1(X)={h1}; skip")
        return None
    theta_V, harm = harmonic_theta(V, edges, val, nfree, Cm)
    theta, sidx = all_theta(R, V, sl, theta_V)
    ok = ~np.isnan(theta)
    Rf = R.astype(np.float32)
    L = R & ~((Rf @ Rf) > 0)  # links
    del Rf
    gi, gj = np.nonzero(L & ok[:, None] & ok[None, :] & (np.abs(sidx[:, None] - sidx[None, :]) <= B))
    jgen = np.round(theta[gi] - theta[gj]).astype(int)  # theta_j + k - theta_i in [-1/2,1/2)
    if dmax is not None:  # order-only safety margin: drop links whose lifted displacement is large
        keepg = np.abs(theta[gj] + jgen - theta[gi]) <= dmax
        gi, gj, jgen = gi[keepg], gj[keepg], jgen[keepg]
    nlinks = int(L.sum())
    # coordinate sheet change on the same generators, for the gauge match
    cgen = np.round(x[gi] - x[gj]).astype(int)
    best = None
    for sgn in (1, -1):
        adj = defaultdict(list)
        for a, b, w_, c_ in zip(gi, gj, jgen, cgen):
            h = w_ - sgn * c_
            adj[a].append((b, h))
            adj[b].append((a, -h))
        delta = {}
        for root in np.flatnonzero(ok):
            if root in delta:
                continue
            delta[root] = 0
            q = deque([root])
            while q:
                u = q.popleft()
                for v, h in adj[u]:
                    if v not in delta:
                        delta[v] = delta[u] + h
                        q.append(v)
        bad = sum(1 for a, b, w_, c_ in zip(gi, gj, jgen, cgen) if w_ - sgn * c_ != delta[b] - delta[a])
        if best is None or bad < best[0]:
            best = (bad, sgn, delta)
    bad, sgn, delta = best
    if not quiet:
        print(f"seed={seed} rho={rho} n={n} B={B}: N={len(t)}, slices={sl.max()+1}, harmonic |resid| max {np.abs(harm).max():.3f};"
              f" generators {len(gi)} of {nlinks} links ({len(gi)/nlinks:.1%}); gauge-mismatched generators {bad}")
    return t, x, R, theta, sidx, ok, gi, gj, jgen, sgn, delta, S


def closure(t, gi, gj, jgen, N, S):
    W = 2 * S + 1
    succ = defaultdict(list)
    for a, b, k in zip(gi, gj, jgen):
        succ[int(a)].append((int(b), int(k)))
    reach = {}
    for u in np.argsort(t)[::-1]:  # any linear extension of the order works
        u = int(u)
        for k in range(-S, S + 1):
            r = 0
            for v, dk in succ[u]:
                kk = k + dk
                if -S <= kk <= S:
                    r |= (1 << (int(v) * W + kk + S)) | reach.get((int(v), kk), 0)
            reach[(u, k)] = r
    return reach


def cover(seeds=(0, 1, 2), rho=3000, n=35, B=5, dmax=None):
    for seed in seeds:
        out = lift(seed, rho, n, B, dmax=dmax)
        if out is None:
            continue
        t, x, R, theta, sidx, ok, gi, gj, jgen, sgn, delta, S = out
        N, W = len(t), 2 * S + 1
        reach = closure(t, gi, gj, jgen, N, S)
        okv = np.flatnonzero(ok & np.array([i in delta for i in range(N)]))
        dl = np.array([delta.get(i, 0) for i in range(N)])
        tab, taub, imgs = Counter(), defaultdict(Counter), Counter()
        nb = (N * W + 7) // 8
        for u in okv:
            ku = sgn * (0 - dl[u])
            r = reach[(int(u), 0)]
            bits = np.unpackbits(np.frombuffer(r.to_bytes(nb, "little"), np.uint8), bitorder="little")[: N * W]
            ordrel = bits.reshape(N, W).astype(bool)
            later = okv[t[okv] > t[u]]
            js = np.arange(-S, S + 1)
            kv = sgn * (js[None, :] - dl[later][:, None])
            d = np.abs(x[later][:, None] + kv - x[u] - ku)
            dt = (t[later] - t[u])[:, None]
            coord = dt > d
            o = ordrel[later]
            tab["TP"] += int((o & coord).sum()); tab["FP"] += int((o & ~coord).sum())
            tab["FN"] += int((~o & coord).sum())
            tau = np.sqrt(np.maximum(dt**2 - d**2, 0))
            tb = np.minimum((tau / 0.05).astype(int), 6)
            for b_ in range(7):
                m = coord & (tb == b_)
                taub[b_]["TP"] += int((o & m).sum()); taub[b_]["FN"] += int((~o & m).sum())
            base = R[u, later]
            nc, no = coord[base].sum(axis=1), o[base].sum(axis=1)
            for a, b in zip(nc, no):
                imgs[(int(a), int(b))] += 1
        fnr = tab["FN"] / max(tab["FN"] + tab["TP"], 1)
        print(f"  entries: {dict(tab)}; FP={tab['FP']}, FN rate {fnr:.2%}")
        print("  FN by tau: " + ", ".join(
            f"[{b*0.05:.2f},{(b+1)*0.05:.2f}){'' if b<6 else '+'} {taub[b]['FN']/max(taub[b]['FN']+taub[b]['TP'],1):.1%}"
            for b in range(7)))
        tot2 = sum(v for (a, b), v in imgs.items() if a == 2)
        print(f"  two-image pairs recovered with 2 sheets: {imgs[(2,2)]}/{tot2} ({imgs[(2,2)]/max(tot2,1):.1%});"
              f" one-image recovered: {imgs[(1,1)]}/{sum(v for (a,b),v in imgs.items() if a==1)}; all: {dict(sorted(imgs.items()))}", flush=True)


def e2e(seeds=(0, 1), rho=1200, n=25, B=5, m=4.0, T=1.2, Phis=(0.0, np.pi / 2, np.pi), dmax=None):
    """Johnston K on the order-built cover vs continuum image sum."""
    for seed in seeds:
        out = lift(seed, rho, n, B, S=2, T=T, dmax=dmax)
        if out is None:
            continue
        t, x, R, theta, sidx, ok, gi, gj, jgen, sgn, delta, S = out
        N, W = len(t), 2 * S + 1
        reach = closure(t, gi, gj, jgen, N, S)
        # cover causal matrix C on nodes (v, k), in a topological order (t, then k)
        nodes = [(int(v), k) for v in np.argsort(t) for k in range(-S, S + 1)]
        idx = {nd: i for i, nd in enumerate(nodes)}
        M = len(nodes)
        nb = (N * W + 7) // 8
        C = np.zeros((M, M), np.float32)
        perm = np.array([v * W + k + S for v, k in nodes])
        for i, (v, k) in enumerate(nodes):
            r = reach.get((v, k), 0)
            if r:
                bits = np.unpackbits(np.frombuffer(r.to_bytes(nb, "little"), np.uint8), bitorder="little")[: N * W]
                C[i] = bits[perm]
        Mx = np.eye(M, dtype=np.float32) + np.float32(m * m / (2 * rho)) * C
        src = np.array([idx[(int(v), 0)] for v in range(N)])
        # rows of K for sources on sheet 0: K[src] = 1/2 C[src] Mx^{-1}  (Mx upper triangular)
        Ks = 0.5 * solve_triangular(Mx.T, C[src].T, lower=True, unit_diagonal=True, check_finite=False).T
        del Mx
        dl = np.array([delta.get(i, 0) for i in range(N)])
        # control: coordinate-built cover on the SAME nodes (gauge-matched)
        nv = np.array([v for v, k in nodes]); nk = np.array([k for v, k in nodes])
        P = x[nv] + sgn * (nk - dl[nv])
        tn = t[nv]
        C = ((tn[None, :] - tn[:, None]) > np.abs(P[None, :] - P[:, None])).astype(np.float32)
        Mx = np.eye(M, dtype=np.float32) + np.float32(m * m / (2 * rho)) * C
        Kc = 0.5 * solve_triangular(Mx.T, C[src].T, lower=True, unit_diagonal=True, check_finite=False).T
        del Mx, C
        rng = np.random.default_rng(seed)
        I, J = np.nonzero(R)
        good = ok[I] & ok[J]
        I, J = I[good], J[good]
        sel = rng.choice(len(I), size=min(len(I), 200000), replace=False)
        I, J = I[sel], J[sel]
        DT = t[J] - t[I]
        res = defaultdict(lambda: defaultdict(list))
        for ph in Phis:
            Kp = np.zeros(len(I), complex)
            Kcp = np.zeros(len(I), complex)
            Gp = np.zeros(len(I), complex)
            nimg = np.zeros(len(I), int)
            for j in range(-S, S + 1):
                cols = np.array([idx[(int(v), j)] for v in J])
                Kp += np.exp(1j * j * ph) * Ks[I, cols]
                Kcp += np.exp(1j * j * ph) * Kc[I, cols]
                # continuum image of order-sheet j: coordinate sheet kv relative to source
                kv = sgn * (j - dl[J]) - sgn * (0 - dl[I])
                d = np.abs(x[J] + kv - x[I])
                inside = d < DT
                Gp += np.where(inside, np.exp(1j * j * ph) * 0.5 * j0(m * np.sqrt(np.maximum(DT**2 - d**2, 0))), 0)
                nimg += inside
            for ni in (1, 2):
                for lo_, hi_ in ((0.3, 0.5), (0.5, 0.7), (0.7, 1.0)):
                    s_ = (nimg == ni) & (DT >= lo_) & (DT < hi_)
                    if s_.sum() > 50:
                        res[(ni, lo_, hi_)][ph] = (s_.sum(), Kp[s_].real.mean(), Gp[s_].real.mean(), Kcp[s_].real.mean())
        print(f"  e2e seed={seed} rho={rho} m={m}: cover nodes {M}")
        print("   images Δt-bin     pairs  " + "  ".join(f"Φ={p:.2f}: K_order / K_coord / continuum" for p in Phis))
        for key in sorted(res):
            ni, lo_, hi_ = key
            row = res[key]
            cnt = next(iter(row.values()))[0]
            print(f"   {ni:5d} [{lo_:.1f},{hi_:.1f}) {cnt:6d}  " + "   ".join(f"{row[p][1]:+.4f} / {row[p][3]:+.4f} / {row[p][2]:+.4f}" for p in Phis))


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "cover"
    {"scan": scan, "cover": cover, "e2e": e2e}[mode]()


def e2e_fourier(seeds=(0, 1, 2), rho=3000, n=25, B=5, dmax=0.25, T=1.2, ms=(0.0, 4.0),
                Phis=(0.0, np.pi / 2, np.pi), S=3, label="", absval=False):
    """End-to-end AB propagator via the deck Fourier transform.

    The lifted relation is deck-invariant, so on the infinite cover
      K_Phi(u,v) = sum_d e^{i d Phi} K_cover((u,0),(v,d))
                 = 1/2 Ĉ_Phi (I + m^2/(2 rho) Ĉ_Phi)^{-1},
      Ĉ_Phi(u,v) = sum_d e^{i d Phi} C_d(u,v),  C_d(u,v) = [(u,0) < (v,d)].
    Computed for the order-built cover, the coordinate cover (control), and
    compared with the continuum sum_d e^{i d Phi} 1/2 J0(m tau_d)."""
    for seed in seeds:
        out = lift(seed, rho, n, B, S=S, T=T, dmax=dmax)
        if out is None:
            continue
        t, x, R, theta, sidx, ok, gi, gj, jgen, sgn, delta, S = out
        N, W = len(t), 2 * S + 1
        reach = closure(t, gi, gj, jgen, N, S)
        o = np.argsort(t)                      # linear extension -> upper triangular
        inv = np.empty(N, int); inv[o] = np.arange(N)
        nb = (N * W + 7) // 8
        Cd = np.zeros((W, N, N), bool)         # in sorted order
        for u in range(N):
            r = reach.get((u, 0), 0)
            if r:
                bits = np.unpackbits(np.frombuffer(r.to_bytes(nb, "little"), np.uint8),
                                     bitorder="little")[: N * W].reshape(N, W)
                Cd[:, inv[u], :] = bits[o].T
        dl = np.array([delta.get(i, 0) for i in range(N)])[o]
        ts, xs, oks = t[o], x[o], ok[o]
        ds = np.arange(-S, S + 1)
        # coordinate cover C_d in the same gauge
        Cc = np.zeros((W, N, N), bool)
        ku = sgn * (0 - dl)
        for a, d in enumerate(ds):
            kv = sgn * (d - dl)
            Cc[a] = (ts[None, :] - ts[:, None]) > np.abs(xs[None, :] + kv[None, :] - xs[:, None] - ku[:, None])
        Rs = R[np.ix_(o, o)]
        I, J = np.nonzero(Rs & oks[:, None] & oks[None, :])
        rng = np.random.default_rng(seed)
        sel = rng.choice(len(I), size=min(len(I), 400000), replace=False)
        I, J = I[sel], J[sel]
        DT = ts[J] - ts[I]
        # continuum images per pair, by order-sheet d
        tau_d, in_d = [], []
        for d in ds:
            kv = sgn * (d - dl[J]) - sgn * (0 - dl[I])
            dd = np.abs(xs[J] + kv - xs[I])
            in_d.append(dd < DT)
            tau_d.append(np.sqrt(np.maximum(DT**2 - dd**2, 0)))
        nimg = np.sum(in_d, axis=0)
        print(f"\n=== e2e (deck Fourier){label}: seed={seed} rho={rho} n={n} B={B} dmax={dmax} N={N},"
              f" elements without theta {int((~ok).sum())}")
        for m in ms:
            a_ = m * m / (2 * rho)
            print(f"  m={m} [{'|K| gauge-invariant' if absval else 'Re K'}]: images Δt-bin  pairs   " + "   ".join(f"Φ={p:.2f}: order / coord / continuum" for p in Phis))
            rows = defaultdict(dict)
            for ph in Phis:
                ph_ = np.exp(1j * ds * ph)
                vals = {}
                for name, CC in (("order", Cd), ("coord", Cc)):
                    Ch = np.tensordot(ph_, CC.astype(np.complex128), axes=1)
                    if a_ > 0:
                        Mx = np.eye(N, dtype=complex) + a_ * Ch
                        # K = 1/2 Ch Mx^{-1}  (both upper triangular, commute)
                        K = 0.5 * solve_triangular(Mx.T, Ch.T, lower=True, unit_diagonal=True, check_finite=False).T
                    else:
                        K = 0.5 * Ch
                    vals[name] = K[I, J]
                    del Ch
                G = sum(ph_[k] * np.where(in_d[k], 0.5 * j0(m * tau_d[k]), 0) for k in range(W))
                for ni in (1, 2, 3):
                    for lo_, hi_ in ((0.3, 0.5), (0.5, 0.7), (0.7, 1.0)):
                        s_ = (nimg == ni) & (DT >= lo_) & (DT < hi_)
                        if s_.sum() > 100:
                            f_ = np.abs if absval else np.real
                            rows[(ni, lo_, hi_)][ph] = (s_.sum(), f_(vals["order"][s_]).mean(),
                                                         f_(vals["coord"][s_]).mean(), f_(G[s_]).mean())
            for key in sorted(rows):
                ni, lo_, hi_ = key
                r_ = rows[key]
                cnt = next(iter(r_.values()))[0]
                print(f"   {ni:5d} [{lo_:.1f},{hi_:.1f}) {cnt:7d}  " + "   ".join(
                    f"{r_[p][1]:+.4f} / {r_[p][2]:+.4f} / {r_[p][3]:+.4f}" for p in Phis), flush=True)


def density_scan(rhos=(1500, 2250, 3000, 4500), seeds=(0, 1, 2, 3), n_at_3000=25, B=5, dmax=0.25,
                 bins=((0.5, 0.6), (0.6, 0.7), (0.7, 0.85), (0.85, 1.0))):
    """Missed-sheet statistics at fixed physical settings: slice spacing 0.05,
    span bound B, margin dmax, and n proportional to rho (constant shadow width).
    Reports, for base pairs with 2 continuum images, per Δt bin: the fraction of
    PAIRS missing >= 1 sheet and the fraction of SHEETS missed."""
    print("rho   seed  n    " + "  ".join(f"Δt[{a:.2f},{b:.2f}) pairs-miss / sheets-miss" for a, b in bins))
    for rho in rhos:
        n = int(round(n_at_3000 * rho / 3000))
        for seed in seeds:
            out = lift(seed, rho, n, B, dmax=dmax, quiet=True)
            if out is None:
                print(f"{rho:5d} {seed:4d} {n:4d}  dim H1(X) != 1", flush=True)
                continue
            t, x, R, theta, sidx, ok, gi, gj, jgen, sgn, delta, S = out
            N, W = len(t), 2 * S + 1
            reach = closure(t, gi, gj, jgen, N, S)
            dl = np.array([delta.get(i, 0) for i in range(N)])
            nb = (N * W + 7) // 8
            acc = [[0, 0, 0] for _ in bins]  # pairs, pairs missing, sheets missed
            fp = 0
            for u in np.flatnonzero(ok):
                r = reach.get((int(u), 0), 0)
                bits = np.unpackbits(np.frombuffer(r.to_bytes(nb, "little"), np.uint8),
                                     bitorder="little")[: N * W].reshape(N, W).astype(bool) if r else np.zeros((N, W), bool)
                vs = np.flatnonzero(R[u] & ok)
                if len(vs) == 0:
                    continue
                ku = sgn * (0 - dl[u])
                js = np.arange(-S, S + 1)
                kv = sgn * (js[None, :] - dl[vs][:, None])
                dt = (t[vs] - t[u])[:, None]
                coord = dt > np.abs(x[vs][:, None] + kv - x[u] - ku)
                o = bits[vs]
                fp += int((o & ~coord).sum())
                nc, no = coord.sum(axis=1), (o & coord).sum(axis=1)
                for k, (a, b) in enumerate(bins):
                    m = (nc == 2) & (dt[:, 0] >= a) & (dt[:, 0] < b)
                    acc[k][0] += int(m.sum()); acc[k][1] += int((no[m] < 2).sum()); acc[k][2] += int((2 - no[m]).sum())
            print(f"{rho:5d} {seed:4d} {n:4d}  " + "  ".join(
                f"{a_[1]/max(a_[0],1):6.2%} / {a_[2]/max(2*a_[0],1):6.2%} (n={a_[0]})" for a_ in acc) + f"   FP={fp}", flush=True)
