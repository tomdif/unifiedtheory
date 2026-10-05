"""Order-only Z-cover at large N without storing the relation matrix.

The causal order is accessed only through a relation ORACLE (`Oracle.rel`),
evaluated on small blocks; nothing of size N^2 is ever stored.  The oracle
computes relations from the sprinkling internally; the construction never
sees coordinates.  Coordinates are used only in `evaluate` (ground truth).

Construction (order only):
  past counts |J-(x)| (blockwise) -> linear extension (sort by |J-|)
  slices: minimal elements of a past-count band, completed greedily to a
          maximal antichain (checked against all elements)
  boundary flag: future count of slice elements < 0.8 x slice median
  thickened antichain T_n inside a layer above the slice (complete because A
          is maximal: every y in J-(x) \\ J-(A) lies in J+(A))
  shadows of maximal elements of T_n; pruning; nerve / witness complex X;
  integral cocycle; harmonic circular coordinate θ
  generators: relations from each element to the next W elements of the
          linear extension, lifted by the nearest rule with |Δθ| <= dmax
  closure: sparse frontier propagation on the 3N-node lifted graph

Usage: python3.11 scripts/ab_cover_sparse.py <rho> <n> <W> [seed ...]
"""
import sys, time
import numpy as np
import scipy.sparse as sp
from collections import defaultdict, Counter, deque
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import lsqr
import ab_order_cover as oc
from ab_cover_2p1 import nerve_b1, circ_mean

Y, T, D = 0.6, 0.75, 3


class Oracle:
    """x_i < x_j query on blocks. Coordinates are private to this class."""
    def __init__(self, rng, rho):
        n = rng.poisson(rho * Y ** (D - 1) * T)
        self._t = rng.uniform(0, T, n).astype(np.float32)
        self._x = rng.uniform(0, 1, n).astype(np.float32)
        self._y = rng.uniform(0, Y, (n, D - 1)).astype(np.float32)
        self.N = n

    def rel(self, I, J):
        I = np.asarray(I); J = np.asarray(J)
        dx = np.abs(self._x[J][None, :] - self._x[I][:, None])
        np.minimum(dx, 1 - dx, out=dx)
        np.multiply(dx, dx, out=dx)                  # dx now holds r^2
        for k in range(D - 1):
            dy = self._y[J, k][None, :] - self._y[I, k][:, None]
            np.multiply(dy, dy, out=dy); dx += dy
            del dy
        dt = self._t[J][None, :] - self._t[I][:, None]
        out = dt > 0
        np.multiply(dt, dt, out=dt)
        out &= dt > dx
        return out

    # ground truth for evaluation only
    def coords(self):
        return self._t.astype(float), self._x.astype(float), self._y.astype(float)


def blockwise_counts(O, rows=2000, cols=2000):
    past = np.zeros(O.N, np.int64)
    allidx = np.arange(O.N)
    for s in range(0, O.N, cols):
        J = allidx[s:s + cols]
        c = np.zeros(len(J), np.int64)
        for r in range(0, O.N, rows):
            c += O.rel(allidx[r:r + rows], J).sum(axis=0)
        past[s:s + cols] = c
    return past


def any_rel(O, I, J, axis, block=2000):
    """For each element of I (axis=0) or J (axis=1): related to ANY of the other set.
    Blocked in both dimensions (at most block x block temporaries)."""
    I = np.asarray(I); J = np.asarray(J)
    out = np.zeros(len(I) if axis == 0 else len(J), bool)
    for a in range(0, len(I), block):
        for b in range(0, len(J), block):
            Rm = O.rel(I[a:a + block], J[b:b + block])
            if axis == 0:
                out[a:a + block] |= Rm.any(axis=1)
            else:
                out[b:b + block] |= Rm.any(axis=0)
    return out


def maximal_slice(O, past, order, k, band_frac=0.04):
    N = O.N
    pos = np.searchsorted(past[order], k)
    band = order[pos:pos + max(int(band_frac * N), 2000)]
    # minimal elements of {past >= k} among the band (complete for band members)
    has_pred = any_rel(O, band, band, axis=1)
    A = list(band[~has_pred])
    # maximality: elements incomparable to all of A, added greedily by |past - k|
    allidx = np.arange(N)
    comp = np.zeros(N, bool)
    comp[A] = True
    for s in range(0, N, 4000):
        blk = allidx[s:s + 4000]
        comp[blk] |= any_rel(O, blk, A, axis=0) | any_rel(O, A, blk, axis=1)
    miss = np.flatnonzero(~comp)
    added = []
    for z in sorted(miss, key=lambda z: abs(past[z] - k)):
        cand = np.array(added) if added else None
        if cand is None or not (O.rel([z], cand).any() or O.rel(cand, [z]).any()):
            added.append(z)
    A = np.array(sorted(A + added))
    return A, len(miss), len(added)


def thickened_shadows(O, past, order, A, n, layer_frac=0.35):
    N = O.N
    allidx = np.arange(N)
    above = np.zeros(N, bool)
    for s in range(0, N, 4000):
        blk = allidx[s:s + 4000]
        above[blk] = any_rel(O, A, blk, axis=1)
    inA = np.zeros(N, bool); inA[A] = True
    kA = np.max(past[A])
    # layer: elements strictly above A with past count up to kA + Δ, Δ grown until T_n is interior
    cand = np.flatnonzero(above & ~inA)
    cand = cand[np.argsort(past[cand])]
    m = max(int(layer_frac * len(cand)), 5 * n)
    while True:
        L = cand[:m]
        # cnt(x) = #{y in L : y < x} + 1  (A maximal => J-(x) \ J-(A) ⊂ J+(A))
        cnt = np.ones(len(L), np.int64)
        for s in range(0, len(L), 300):
            for c0 in range(0, len(L), 20000):
                cnt[c0:c0 + 20000] += O.rel(L[s:s + 300], L[c0:c0 + 20000]).sum(axis=0)
        Tn = L[cnt <= n]
        if len(Tn) == 0 or past[Tn].max() < past[L].max() or m >= len(cand):
            break
        m = min(len(cand), 2 * m)
    # maximal elements of T_n
    has_succ = any_rel(O, Tn, Tn, axis=0)
    M = Tn[~has_succ]
    if len(M) > 3000:                               # order-only random subsample
        M = np.random.default_rng(len(M)).choice(M, 3000, replace=False)
    pos = {a: k for k, a in enumerate(A)}
    sh = []
    for s in range(0, len(M), 500):
        Rm = O.rel(A, M[s:s + 500])           # |A| x block
        for c in range(Rm.shape[1]):
            idx = np.flatnonzero(Rm[:, c])
            if len(idx):
                sh.append(frozenset(idx.tolist()))
    sh = list(set(sh))
    sh = [s for s in sh if not any(s < s2 for s2 in sh)] if len(sh) < 3000 else sh
    return sh, len(L), len(Tn), len(M)


def prune(sh, flags, big=2.0, overlap=0.7, seed=0, cap=3000):
    bad = set(np.flatnonzero(flags))
    sh = [s for s in sh if not (s & bad)]
    if not sh:
        return sh
    rng = np.random.default_rng(seed)
    if len(sh) > cap:
        sh = [sh[i] for i in rng.choice(len(sh), cap, replace=False)]
    med = np.median([len(s) for s in sh])
    sh = [s for s in sh if len(s) <= big * med]
    kept = []
    for i in rng.permutation(len(sh)):
        s = sh[i]
        if all(len(s & k) <= overlap * len(s) for k in kept):
            kept.append(s)
    return kept


def complex_X(O, slices, shad):
    vid, verts = {}, []
    for s, sh in enumerate(shad):
        for m in range(len(sh)):
            vid[(s, m)] = len(verts); verts.append((s, m))
    edges, cells, per_slice = set(), set(), []
    for s, sh in enumerate(shad):
        b0, b1, E, Tr = nerve_b1(len(sh), sh)
        per_slice.append((b0, b1))
        for i, j in E:
            edges.add((vid[(s, i)], vid[(s, j)]))
        for i, j, k in Tr:
            cells.add((vid[(s, i)], vid[(s, j)], vid[(s, k)]))
    for s in range(len(slices) - 1):
        A, B_ = slices[s], slices[s + 1]
        if not shad[s] or not shad[s + 1]:
            continue
        Rab = O.rel(A, B_)
        inA, inB = defaultdict(list), defaultdict(list)
        for m_, sh in enumerate(shad[s]):
            for a in sh:
                inA[a].append(m_)
        for k, sh in enumerate(shad[s + 1]):
            for b in sh:
                inB[b].append(k)
        for a in range(len(A)):
            ms = inA.get(a)
            if not ms:
                continue
            ks = set()
            for b in np.flatnonzero(Rab[a]):
                kb = inB.get(b, [])
                ks.update(kb)
                for i1 in range(len(kb)):
                    for i2 in range(i1 + 1, len(kb)):
                        for m_ in ms:
                            cells.add(tuple(sorted((vid[(s, m_)], vid[(s + 1, kb[i1])], vid[(s + 1, kb[i2])]))))
            for m_ in ms:
                for k in ks:
                    u, v = vid[(s, m_)], vid[(s + 1, k)]
                    edges.add((min(u, v), max(u, v)))
            for i1 in range(len(ms)):
                for i2 in range(i1 + 1, len(ms)):
                    for k in ks:
                        cells.add(tuple(sorted((vid[(s, ms[i1])], vid[(s, ms[i2])], vid[(s + 1, k)]))))
    edges = sorted(edges)
    nbr = defaultdict(set)
    for i, j in edges:
        nbr[i].add(j); nbr[j].add(i)
    return verts, edges, [list(c) for c in cells], nbr, per_slice


def build(O, n, qs, log):
    t0 = time.time()
    past = blockwise_counts(O)
    order = np.argsort(past, kind="stable")
    log(f"  past counts done ({time.time()-t0:.0f}s)")
    slices, shad, owner = [], [], {}
    for si, q in enumerate(qs):
        k = float(np.quantile(past, q))
        A, miss, added = maximal_slice(O, past, order, k)
        A = np.array([a for a in A if a not in owner])
        for a in A:
            owner[a] = si
        fut = np.zeros(len(A), np.int64)
        allidx = np.arange(O.N)
        for s in range(0, O.N, 4000):
            fut += O.rel(A, allidx[s:s + 4000]).sum(axis=1)
        flags = fut < 0.8 * np.median(fut)
        sh, nL, nT, nM = thickened_shadows(O, past, order, A, n)
        sh = prune(sh, flags, seed=si)
        slices.append(A); shad.append(sh)
        log(f"  slice {si}: |A|={len(A)} (greedy +{added}), flagged {flags.mean():.0%}, layer {nL}, |T_n|={nT}, maximal {nM},"
            f" kept shadows {len(sh)} ({time.time()-t0:.0f}s)")
    return past, order, slices, shad


def theta_all(O, past, slices, shad, verts, thv):
    N = O.N
    vid = {v: k for k, v in enumerate(verts)}
    theta = np.full(N, np.nan); sidx = np.full(N, -1)
    for s, (A, sh) in enumerate(zip(slices, shad)):
        acc = defaultdict(list)
        for m, sset in enumerate(sh):
            for a in sset:
                acc[a].append(thv[vid[(s, m)]])
        for a, ths in acc.items():
            theta[A[a]] = circ_mean(ths); sidx[A[a]] = s
    mem = [A[~np.isnan(theta[A])] for A in slices]
    cs = [np.cos(2 * np.pi * theta[m]).astype(np.float32) for m in mem]
    sn = [np.sin(2 * np.pi * theta[m]).astype(np.float32) for m in mem]
    todo = np.flatnonzero(np.isnan(theta))
    levels = np.array([np.median(past[m]) if len(m) else np.inf for m in mem])
    for s in range(len(mem) - 1, -1, -1):          # highest slice with elements in the past
        if len(mem[s]) == 0 or len(todo) == 0:
            continue
        cand = todo[past[todo] >= levels[s]]
        for b in range(0, len(cand), 1500):
            V = cand[b:b + 1500]
            Rm = O.rel(mem[s], V).astype(np.float32)
            cnt = Rm.sum(axis=0)
            zr = cs[s] @ Rm; zi = sn[s] @ Rm
            del Rm
            hit = cnt > 0
            theta[V[hit]] = np.mod(np.arctan2(zi[hit], zr[hit]) / (2 * np.pi), 1.0)
            sidx[V[hit]] = s
        todo = np.flatnonzero(np.isnan(theta))
    if len(todo) and len(mem[0]):                  # below the lowest slice: future shadow
        for b in range(0, len(todo), 1500):
            V = todo[b:b + 1500]
            Rm = O.rel(V, mem[0]).astype(np.float32)
            cnt = Rm.sum(axis=1)
            zr = Rm @ cs[0]; zi = Rm @ sn[0]
            del Rm
            hit = cnt > 0
            theta[V[hit]] = np.mod(np.arctan2(zi[hit], zr[hit]) / (2 * np.pi), 1.0)
            sidx[V[hit]] = 0
    return theta, sidx


def link_generators(O, order, theta, Wn, dmax, blk=200, log=print):
    """Exact links i -> j for j within the next Wn elements of the linear
    extension: j is a minimal element of J+(i) ∩ window (complete for that
    window, since any i < k < j lies between i and j in the extension)."""
    N = O.N
    ok = ~np.isnan(theta)
    gi, gj, gk = [], [], []
    t0 = time.time()
    for b in range(0, N, blk):
        I = order[b:b + blk]
        J = order[b + 1:min(N, b + blk + Wn)]
        if len(J) == 0:
            continue
        Rm = O.rel(I, J)
        for r, i in enumerate(I):
            lo = r                                   # J index of position b+r+1 is r
            Sidx = np.flatnonzero(Rm[r, lo:lo + Wn]) + lo
            if len(Sidx) == 0:
                continue
            S = J[Sidx]
            minimal = ~O.rel(S, S).any(axis=0)
            L = S[minimal]
            m = ok[L] & ok[i]
            L = L[m]
            k = np.round(theta[i] - theta[L]).astype(np.int64)
            keep = np.abs(theta[L] + k - theta[i]) <= dmax
            gi.append(np.full(int(keep.sum()), i, np.int32)); gj.append(L[keep].astype(np.int32)); gk.append(k[keep].astype(np.int8))
        if b % (blk * 50) == 0:
            log(f"    links: {b}/{N} ({time.time()-t0:.0f}s)")
    return np.concatenate(gi), np.concatenate(gj), np.concatenate(gk)


def generators(O, order, theta, Wn, dmax, K=None):
    N = O.N
    gi, gj, gk = [], [], []
    ok = ~np.isnan(theta)
    for b in range(0, N, 1000):
        I = order[b:b + 1000]
        J = order[b + 1:min(N, b + 1000 + Wn)]
        if len(J) == 0:
            continue
        Rm = O.rel(I, J)
        # only the next Wn in the linear extension for each i
        pi = np.arange(b, b + len(I))[:, None]; pj = np.arange(b + 1, b + 1 + len(J))[None, :]
        Rm &= (pj > pi) & (pj <= pi + Wn)
        if K is not None:      # keep the K related successors with smallest past-count increment
            Rm &= np.cumsum(Rm, axis=1) <= K
        a, c = np.nonzero(Rm)
        a, c = I[a], J[c]
        m = ok[a] & ok[c]
        a, c = a[m], c[m]
        k = np.round(theta[a] - theta[c]).astype(np.int64)
        keep = np.abs(theta[c] + k - theta[a]) <= dmax
        gi.append(a[keep]); gj.append(c[keep]); gk.append(k[keep])
    return np.concatenate(gi), np.concatenate(gj), np.concatenate(gk)


def evaluate(O, theta, gi, gj, gk, n_src=64, S=1, seed=0, log=print):
    t, x, Yc = O.coords()
    N = O.N
    ok = ~np.isnan(theta)
    # gauge match (diagnostic, coordinates), graph-free: theta ≈ sg*x + off (mod 1),
    # so each element's sheet offset is delta_v = round(sg*x_v + off - theta_v);
    # a generator is genuinely mislifted iff gk != sg*c + delta_b - delta_a.
    cg = np.round(x[gi] - x[gj]).astype(np.int64)
    best = None
    for sg in (1, -1):
        off = np.angle(np.exp(2j * np.pi * (theta[ok] - sg * x[ok])).mean()) / (2 * np.pi)
        delta = np.zeros(N, np.int64)
        delta[ok] = np.round(sg * x[ok] + off - theta[ok]).astype(np.int64)
        bad = int(np.sum(gk.astype(np.int64) - sg * cg != delta[gj] - delta[gi]))
        if best is None or bad < best[0]:
            best = (bad, sg, delta)
    bad, sgn, delta = best
    dl = delta
    log(f"  [eval] generators {len(gi)}; gauge-mismatched {bad}")
    W = 2 * S + 1
    # base-size adjacency per sheet shift dk: (a, k) -> (b, k + dk)
    AT = {dk: sp.csr_matrix((np.ones(int((gk == dk).sum()), np.float32), (gj[gk == dk], gi[gk == dk])), shape=(N, N))
          for dk in (-1, 0, 1)}
    del cg
    rng = np.random.default_rng(seed)
    low = np.flatnonzero(ok & (t < 0.2))          # evaluation-only choice: early sources see two images
    src = rng.choice(low, size=min(n_src, len(low)), replace=False)
    ns = len(src)
    reach = np.zeros((N, W, ns), bool)
    front = np.zeros((N, W, ns), np.float32)
    front[src, S, np.arange(ns)] = 1.0
    it = 0
    while front.any():
        nxt = np.zeros((N, W, ns), bool)
        for k in range(W):
            for dk, M in AT.items():
                k0 = k - dk                           # (a, k0) -> (b, k0 + dk = k)
                if 0 <= k0 < W:
                    nxt[:, k, :] |= (M @ front[:, k0, :]) > 0
        nxt &= ~reach
        reach |= nxt
        front = nxt.astype(np.float32)
        it += 1
    log(f"  [eval] closure: {it} frontier iterations for {len(src)} sources")
    js = np.arange(-S, S + 1)
    inner = np.all((Yc > 0.15) & (Yc < Y - 0.15), axis=1)
    out = {}
    for key in ("all", "interior"):
        tab = Counter(); two = [0, 0, 0]; taub = defaultdict(Counter)
        for c, u in enumerate(src):
            if key == "interior" and not inner[u]:
                continue
            vs = np.flatnonzero(ok & (t > t[u]))
            ku = sgn * (0 - dl[u]); kv = sgn * (js[None, :] - dl[vs][:, None])
            sp2 = (x[vs][:, None] + kv - x[u] - ku) ** 2 + ((Yc[vs] - Yc[u]) ** 2).sum(axis=1)[:, None]
            dt = (t[vs] - t[u])[:, None]
            coord = dt > np.sqrt(sp2)
            o = reach[vs][:, :, c]
            tab["TP"] += int((o & coord).sum()); tab["FP"] += int((o & ~coord).sum()); tab["FN"] += int((~o & coord).sum())
            tau = np.sqrt(np.maximum(dt ** 2 - sp2, 0)); tb = np.minimum((tau / 0.05).astype(int), 6)
            for b_ in range(7):
                mm = coord & (tb == b_)
                taub[b_]["TP"] += int((o & mm).sum()); taub[b_]["FN"] += int((~o & mm).sum())
            nc, no = coord.sum(axis=1), (o & coord).sum(axis=1)
            m2 = nc == 2
            two[0] += int(m2.sum()); two[1] += int((no[m2] < 2).sum()); two[2] += int((2 - no[m2]).sum())
        fnr = tab["FN"] / max(tab["FN"] + tab["TP"], 1)
        log(f"  [eval:{key}] FP={tab['FP']} of {tab['TP']+tab['FP']}; FN {fnr:.2%}; FN by tau "
            + ", ".join(f"{taub[b]['FN']/max(taub[b]['FN']+taub[b]['TP'],1):.1%}" for b in range(7))
            + f"; two-image pairs {two[0]}: missing a sheet {two[1]/max(two[0],1):.2%}, sheets missed {two[2]/max(2*two[0],1):.2%}")
    return out


def main(rho, n, Wn, seeds, qs=np.linspace(0.13, 0.67, 9), dmax=0.25, K=None, links=True):
    for seed in seeds:
        import resource
        log = lambda s: print(f"{s}   [peak {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1e9:.2f} GB]", flush=True)
        rng = np.random.default_rng(seed)
        O = Oracle(rng, rho)
        log(f"=== sparse 3+1 seed={seed} rho={rho} n={n} W={Wn}: N={O.N}")
        past, order, slices, shad = build(O, n, qs, log)
        verts, edges, cells, nbr, per_slice = complex_X(O, slices, shad)
        val, nfree, rank, _, conn, Cm = oc.cocycle(len(verts), edges, cells, nbr)
        h1 = nfree - rank
        log(f"  per-slice nerve {dict(Counter(per_slice))}; X {len(verts)}v/{len(edges)}e/{len(cells)}c; dim H^1(X)={h1}")
        if h1 != 1:
            continue
        g = np.array([1, 1])
        if nfree != 1:
            _, sv, Vt = np.linalg.svd(Cm[:, 1:].astype(float))
            gg = Vt[-1] / np.min(np.abs(Vt[-1][np.abs(Vt[-1]) > 1e-6]))
            g = np.concatenate([[1], np.round(gg).astype(int)])
        w = np.array([np.pad(val[e], (0, 1 + nfree - len(val[e]))) @ g for e in edges], float)
        E = len(edges)
        Dm = coo_matrix((np.tile([-1.0, 1.0], E), (np.repeat(np.arange(E), 2), np.array(edges).ravel())),
                        shape=(E, len(verts))).tocsr()
        thv = np.mod(lsqr(Dm, -w, atol=1e-12, btol=1e-12, iter_lim=50000)[0], 1.0)
        log("  (stage) harmonic theta on X done")
        del cells, val, Cm
        theta, sidx = theta_all(O, past, slices, shad, verts, thv)
        log("  (stage) theta_all done")
        t, x, _ = O.coords()
        okm = ~np.isnan(theta)
        for sg in (1, -1):
            off = np.angle(np.exp(2j * np.pi * (theta[okm] - sg * x[okm])).mean()) / (2 * np.pi)
            err = np.abs(np.angle(np.exp(2j * np.pi * (theta[okm] - sg * x[okm] - off))) / (2 * np.pi))
            if np.median(err) < 0.2:
                log(f"  [eval] theta vs coordinate: |err| median {np.median(err):.3f}, 99% {np.quantile(err,.99):.3f}, max {err.max():.3f}; defined for {okm.mean():.1%}")
        gi, gj, gk = (link_generators(O, order, theta, Wn, dmax, log=log) if links
                      else generators(O, order, theta, Wn, dmax, K=K))
        evaluate(O, theta, gi, gj, gk, seed=seed, log=log)


if __name__ == "__main__":
    rho, n, Wn, K = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    seeds = [int(s) for s in sys.argv[5:]] or [0]
    main(rho, n, Wn, seeds, K=(K if K > 0 else None))
