"""Order-only Z-cover in flat (d)+1 with one compact dimension, NO coordinates
in the construction.

Spacetime: S^1_x (L = 1) × [0, Y]^(d-1) × [0, T].  d = 2 (2+1) or d = 3 (3+1).

Construction (order only):
 * linear extension: sort by past cardinality |J-(x)| (x < y ⇒ |J-(x)| < |J-(y)|);
 * slice levels: quantiles of the past-cardinality distribution;
 * slices: maximal antichains at those levels (greedy extension);
 * boundary: on a past-cardinality level set, elements near the region's edge
   sit later and have truncated futures, so their FUTURE cardinality is
   anomalously low; shadows containing such slice elements are dropped
   (replaces the coordinate y-buffer of ab_cover_2p1);
 * shadows / nerve / witness cells / cocycle / harmonic θ / nearest-rule lift /
   closure exactly as in ab_cover_2p1, with no coordinate input.
Coordinates are used ONLY in the evaluation (ground-truth cover comparison),
reported for all sources and for an interior band.

Usage: python3.11 scripts/ab_cover_nd.py <d> <rho> <n> [seeds...]
"""
import sys
import numpy as np
from collections import deque, defaultdict, Counter
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import lsqr
import ab_order_cover as oc
from ab_slicing_and_images import maximal_slice
from ab_chain_pair_holonomy import shadows
from ab_cover_2p1 import nerve_b1, complex_X, links_packed, circ_mean


def sprinkle(rng, rho, d, Y, T, block=800):
    n = rng.poisson(rho * Y ** (d - 1) * T)
    t = np.sort(rng.uniform(0, T, n)).astype(np.float32)
    x = rng.uniform(0, 1, n).astype(np.float32)
    Ys = rng.uniform(0, Y, (n, d - 1)).astype(np.float32)
    R = np.zeros((n, n), bool)
    for s in range(0, n, block):
        e = min(n, s + block)
        dx = np.abs(x[None, :] - x[s:e, None]); dx = np.minimum(dx, 1 - dx)
        r2 = dx * dx
        for k in range(d - 1):
            dy = Ys[None, :, k] - Ys[s:e, None, k]
            r2 = r2 + dy * dy
        R[s:e] = (t[None, :] - t[s:e, None]) > np.sqrt(r2)
    # shuffle labels so that index order carries no time information
    perm = rng.permutation(n)
    R = R[np.ix_(perm, perm)]
    return t[perm].astype(float), x[perm].astype(float), Ys[perm].astype(float), R


def build_order_only(R, n, qs, fut_frac=0.8, big=2.0, overlap=0.7):
    past = R.sum(axis=0)
    fut = R.sum(axis=1)
    slices, owner, flags = [], {}, []
    for q in qs:
        k = float(np.quantile(past, q))
        A, _, _ = maximal_slice(R, past, k)
        A = np.array([a for a in A if a not in owner])
        for a in A:
            owner[a] = len(slices)
        slices.append(A)
        # boundary flag: future cardinality well below the slice median
        flags.append(fut[A] < fut_frac * np.median(fut[A]))
    shad = []
    for s, A in enumerate(slices):
        raw = shadows(R, A, n)
        bad = set(np.flatnonzero(flags[s]))
        raw = [sh for sh in raw if not (sh & bad)]
        if raw:
            med = np.median([len(x) for x in raw])
            raw = [x for x in raw if len(x) <= big * med]
        rng = np.random.default_rng(s)
        kept = []
        for i in rng.permutation(len(raw)):
            sh = raw[i]
            if all(len(sh & k) <= overlap * len(sh) for k in kept):
                kept.append(sh)
        shad.append(kept)
    return slices, shad, past, flags


def run(d, rho, n, seeds, Y=0.6, T=0.8, qs=None, B=4, dmax=0.25, S=1, interior=0.15):
    qs = qs if qs is not None else np.linspace(0.125, 0.75, 11)
    for seed in seeds:
        rng = np.random.default_rng(seed)
        t, x, Ys, R = sprinkle(rng, rho, d, Y, T)
        N = len(t)
        slices, shad, past, flags = build_order_only(R, n, qs)
        verts, edges, cells, nbr, per_slice = complex_X(R, slices, shad)
        val, nfree, rank, _, conn, Cm = oc.cocycle(len(verts), edges, cells, nbr)
        h1 = nfree - rank
        tl = [f"{t[A].mean():.2f}" for A in slices]
        print(f"\n=== {d}+1 seed={seed} rho={rho} n={n}: N={N}, slices={len(slices)} (mean t {', '.join(tl)} — diagnostic),"
              f" boundary-flagged {np.mean([f.mean() for f in flags]):.1%} of slice elements,"
              f" shadows/slice ~{np.mean([len(s) for s in shad]):.0f}, per-slice nerve {dict(Counter(per_slice))},"
              f" X {len(verts)}v/{len(edges)}e/{len(cells)}c, dim H^1(X)={h1}", flush=True)
        if h1 != 1:
            continue
        g = np.array([1, 1])
        if nfree != 1:
            _, sv, Vt = np.linalg.svd(Cm[:, 1:].astype(float))
            gg = Vt[-1] / np.min(np.abs(Vt[-1][np.abs(Vt[-1]) > 1e-6]))
            g = np.concatenate([[1], np.round(gg).astype(int)])
        w = np.array([np.pad(val[e], (0, 1 + nfree - len(val[e]))) @ g for e in edges], float)
        E = len(edges)
        D = coo_matrix((np.tile([-1.0, 1.0], E), (np.repeat(np.arange(E), 2), np.array(edges).ravel())),
                       shape=(E, len(verts))).tocsr()
        thv = np.mod(lsqr(D, -w, atol=1e-12, btol=1e-12, iter_lim=50000)[0], 1.0)
        theta = np.full(N, np.nan); sidx = np.full(N, -1)
        vid = {v: k for k, v in enumerate(verts)}
        for s, (A, sh) in enumerate(zip(slices, shad)):
            acc = defaultdict(list)
            for m, sset in enumerate(sh):
                for a in sset:
                    acc[a].append(thv[vid[(s, m)]])
            for a, ths in acc.items():
                theta[A[a]] = circ_mean(ths); sidx[A[a]] = s
        mem = [A[~np.isnan(theta[A])] for A in slices]
        for v in range(N):
            if not np.isnan(theta[v]):
                continue
            for s in range(len(slices) - 1, -1, -1):
                mm = R[mem[s], v]
                if mm.any():
                    theta[v], sidx[v] = circ_mean(theta[mem[s][mm]]), s
                    break
            else:
                mm = R[v, mem[0]]
                if mm.any():
                    theta[v], sidx[v] = circ_mean(theta[mem[0][mm]]), 0
        ok = ~np.isnan(theta)
        li, lj = links_packed(R)
        keep = ok[li] & ok[lj] & (np.abs(sidx[li] - sidx[lj]) <= B)
        li, lj = li[keep], lj[keep]
        jg = np.round(theta[li] - theta[lj]).astype(int)
        keep = np.abs(theta[lj] + jg - theta[li]) <= dmax
        gi, gj, jgen = li[keep], lj[keep], jg[keep]
        # ---------------- evaluation only (coordinates) ----------------
        for sg in (1, -1):
            off = np.angle(np.exp(2j * np.pi * (theta[ok] - sg * x[ok])).mean()) / (2 * np.pi)
            err = np.abs(np.angle(np.exp(2j * np.pi * (theta[ok] - sg * x[ok] - off))) / (2 * np.pi))
            if np.median(err) < 0.2:
                print(f"  [eval] theta vs coordinate: |err| median {np.median(err):.3f}, 99% {np.quantile(err, .99):.3f}, max {err.max():.3f}; theta defined for {ok.mean():.1%} of elements")
        cgen = np.round(x[gi] - x[gj]).astype(int)
        best = None
        for sg in (1, -1):
            adj = defaultdict(list)
            for a, b, w_, c_ in zip(gi, gj, jgen, cgen):
                h = int(w_ - sg * c_); adj[int(a)].append((int(b), h)); adj[int(b)].append((int(a), -h))
            delta = {}
            for root in np.flatnonzero(ok):
                root = int(root)
                if root in delta:
                    continue
                delta[root] = 0; q = deque([root])
                while q:
                    u = q.popleft()
                    for v, h in adj[u]:
                        if v not in delta:
                            delta[v] = delta[u] + h; q.append(v)
            bad = sum(1 for a, b, w_, c_ in zip(gi, gj, jgen, cgen) if w_ - sg * c_ != delta[int(b)] - delta[int(a)])
            if best is None or bad < best[0]:
                best = (bad, sg, delta)
        bad, sgn, delta = best
        print(f"  generators {len(gi)} (links {len(li)} span-eligible); [eval] gauge-mismatched {bad}", flush=True)
        W = 2 * S + 1
        succ = defaultdict(list)
        for a, b, k in zip(gi, gj, jgen):
            succ[int(a)].append((int(b), int(k)))
        reach = {}
        for u in np.argsort(past)[::-1]:           # order-only linear extension
            u = int(u)
            for k in range(-S, S + 1):
                r = 0
                for v, dk in succ[u]:
                    kk = k + dk
                    if -S <= kk <= S:
                        r |= (1 << (v * W + kk + S)) | reach.get((v, kk), 0)
                reach[(u, k)] = r
        dl = np.array([delta.get(i, 0) for i in range(N)])
        nb = (N * W + 7) // 8
        js = np.arange(-S, S + 1)
        inner = np.all((Ys > interior) & (Ys < Y - interior), axis=1)
        stats = {"all": [Counter(), [0, 0, 0], defaultdict(Counter)], "interior": [Counter(), [0, 0, 0], defaultdict(Counter)]}
        for u in np.flatnonzero(ok):
            r = reach.get((int(u), 0), 0)
            bits = (np.unpackbits(np.frombuffer(r.to_bytes(nb, "little"), np.uint8), bitorder="little")[: N * W]
                    .reshape(N, W).astype(bool)) if r else np.zeros((N, W), bool)
            vs = np.flatnonzero(ok & (t > t[u]))
            ku = sgn * (0 - dl[u]); kv = sgn * (js[None, :] - dl[vs][:, None])
            sp2 = (x[vs][:, None] + kv - x[u] - ku) ** 2 + ((Ys[vs] - Ys[u]) ** 2).sum(axis=1)[:, None]
            dt = (t[vs] - t[u])[:, None]
            coord = dt > np.sqrt(sp2)
            o = bits[vs]
            tau = np.sqrt(np.maximum(dt ** 2 - sp2, 0)); tb = np.minimum((tau / 0.05).astype(int), 6)
            base = R[u, vs]
            nc, no = coord[base].sum(axis=1), (o & coord)[base].sum(axis=1)
            m2 = nc == 2
            for key in (["all", "interior"] if inner[u] else ["all"]):
                tab, two, taub = stats[key]
                tab["TP"] += int((o & coord).sum()); tab["FP"] += int((o & ~coord).sum()); tab["FN"] += int((~o & coord).sum())
                two[0] += int(m2.sum()); two[1] += int((no[m2] < 2).sum()); two[2] += int((2 - no[m2]).sum())
                for b_ in range(7):
                    mm = coord & (tb == b_)
                    taub[b_]["TP"] += int((o & mm).sum()); taub[b_]["FN"] += int((~o & mm).sum())
        for key, (tab, two, taub) in stats.items():
            fnr = tab["FN"] / max(tab["FN"] + tab["TP"], 1)
            print(f"  [eval:{key} sources] FP={tab['FP']} of {tab['TP']+tab['FP']} lifted relations; FN {fnr:.2%};"
                  f" FN by tau " + ", ".join(f"{taub[b]['FN']/max(taub[b]['FN']+taub[b]['TP'],1):.1%}" for b in range(7)) +
                  f"; two-image pairs {two[0]}: missing a sheet {two[1]/max(two[0],1):.2%}, sheets missed {two[2]/max(2*two[0],1):.2%}", flush=True)


if __name__ == "__main__":
    d, rho, n = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    seeds = [int(s) for s in sys.argv[4:]] or [0]
    if d == 2:
        run(2, rho, n, seeds)
    else:
        run(3, rho, n, seeds, Y=0.6, T=0.75, qs=np.linspace(0.13, 0.67, 9), B=4)


def window(d, rho, ns, seed=0, Y=0.6, T=0.75, qs=None):
    """Topology-only scan: per-slice nerve Betti numbers and dim H^1(X) vs n."""
    qs = qs if qs is not None else np.linspace(0.13, 0.67, 9)
    rng = np.random.default_rng(seed)
    t, x, Ys, R = sprinkle(rng, rho, d, Y, T)
    print(f"window {d}+1 rho={rho} seed={seed}: N={len(t)}", flush=True)
    for n in ns:
        slices, shad, past, flags = build_order_only(R, n, qs)
        verts, edges, cells, nbr, per_slice = complex_X(R, slices, shad)
        val, nfree, rank, _, conn, Cm = oc.cocycle(len(verts), edges, cells, nbr)
        sizes = [np.median([len(s) for s in sh]) if sh else 0 for sh in shad]
        print(f"  n={n:4d}: shadows/slice ~{np.mean([len(s) for s in shad]):.0f} (median size {np.mean(sizes):.0f}),"
              f" per-slice nerve {dict(Counter(per_slice))}, X {len(verts)}v/{len(edges)}e, dim H^1(X)={nfree - rank}", flush=True)
