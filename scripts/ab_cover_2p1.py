"""Order-only Z-cover in flat 2+1 with one compact dimension (S^1_x × [0,Y]_y × [0,T]_t).

This is the case Schmitzer (2010, §4.3) and Bogaardt (2013, §3.7) leave open:
their order-only zone algorithm for the homotopy matrix works only in 1+1.

Pipeline (coordinates used only to pick slice LEVELS, as a linear extension,
to restrict test sources to the central y band, and for the comparison):
 1. Slices: maximal antichains at past-cardinality levels, spacing ~0.05 in t.
 2. Per slice: thickened-antichain shadows (MRS) of the maximal elements of T_n.
 3. Complex X on shadows: intra-slice edges/triangles = true nerve (common
    element); inter-slice edges between adjacent slices when some element of
    one shadow precedes some element of the other; inter-slice 2-cells =
    3-cliques (short).  Check dim H^1(X) = 1.
 4. Integral cocycle by flatness propagation; harmonic circular coordinate on
    shadows; circular means down to slice elements, then to off-slice
    elements via their past shadow on the highest slice below.
 5. Generators: base links with slice span <= B and lifted |Δθ| <= dmax,
    lifted by the nearest rule; transitive closure on sheets -1..1.
 6. Compare with the coordinate cover: FP, FN (by proper time), and for pairs
    with two continuum images the pair-miss and sheet-miss fractions.

Usage: python3.11 scripts/ab_cover_2p1.py window | run
"""
import sys
import numpy as np
from collections import deque, defaultdict, Counter
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import lsqr
import ab_order_cover as oc
from ab_slicing_and_images import maximal_slice
from ab_chain_pair_holonomy import shadows
from ab_order_complex_h1 import gf2_rank

Y, T = 0.6, 0.8


def sprinkle21(rng, rho, Y=Y, T=T, block=1000):
    n = rng.poisson(rho * Y * T)
    t = np.sort(rng.uniform(0, T, n))
    x = rng.uniform(0, 1, n).astype(np.float32)
    y = rng.uniform(0, Y, n).astype(np.float32)
    t32 = t.astype(np.float32)
    R = np.zeros((n, n), bool)
    for s in range(0, n, block):
        e = min(n, s + block)
        dx = np.abs(x[None, :] - x[s:e, None])
        dx = np.minimum(dx, 1 - dx)
        dy = y[None, :] - y[s:e, None]
        R[s:e] = (t32[None, :] - t32[s:e, None]) > np.sqrt(dx * dx + dy * dy)
    return t, x.astype(float), y.astype(float), R


def build_slices(t, y, R, n, ts, buf=0.04):
    past = R.sum(axis=0)
    central = (y > 0.2) & (y < Y - 0.2)
    slices, owner = [], {}
    for tt in ts:
        sel = central & (np.abs(t - tt) < 0.01)
        k = float(np.median(past[sel]))
        A, _, _ = maximal_slice(R, past, k)
        A = np.array([a for a in A if a not in owner])
        for a in A:
            owner[a] = len(slices)
        slices.append(A)
    # Region: keep shadows that do not touch the y-boundary layer (|y| < buf from
    # an edge).  Boundary elements have truncated pasts, climb higher in T_n and
    # cast half-disc shadows that are wide in x.  Using y here only delimits the
    # analysed region, as if a larger region had been sprinkled.
    shad = []
    for s, A in enumerate(slices):
        raw = shadows(R, A, n)
        raw = [sh for sh in raw if y[A[list(sh)]].min() >= buf and y[A[list(sh)]].max() <= Y - buf]
        shad.append(prune_shadows(raw, seed=s))
    return slices, shad


def prune_shadows(sh, big=2.0, overlap=0.7, seed=0):
    """Order-only pruning: (1) drop shadows larger than big x median size
    (truncated pasts at the y-edges make boundary shadows huge and can wrap
    the circle); (2) greedy thinning of near-duplicates: skip a shadow if more
    than `overlap` of it lies inside one kept shadow."""
    if not sh:
        return sh
    sizes = np.array([len(s) for s in sh])
    med = np.median(sizes)
    cand = [s for s in sh if len(s) <= big * med]
    rng = np.random.default_rng(seed)
    kept = []
    for i in rng.permutation(len(cand)):
        s = cand[i]
        if all(len(s & k) <= overlap * len(s) for k in kept):
            kept.append(s)
    return kept


def nerve_b1(nsh, sh):
    elems = defaultdict(list)
    for m, s in enumerate(sh):
        for a in s:
            elems[a].append(m)
    E, Tr = set(), set()
    for a, ms in elems.items():
        ms = sorted(ms)
        for i in range(len(ms)):
            for j in range(i + 1, len(ms)):
                E.add((ms[i], ms[j]))
                for k in range(j + 1, len(ms)):
                    Tr.add((ms[i], ms[j], ms[k]))
    E, Tr = sorted(E), sorted(Tr)
    eid = {e: k for k, e in enumerate(E)}
    r1 = gf2_rank([(1 << i) | (1 << j) for i, j in E])
    r2 = gf2_rank([(1 << eid[(i, j)]) | (1 << eid[(j, k)]) | (1 << eid[(i, k)]) for i, j, k in Tr])
    return nsh - r1, len(E) - r1 - r2, E, Tr


def complex_X(R, slices, shad):
    vid, verts = {}, []
    for s, sh in enumerate(shad):
        for m in range(len(sh)):
            vid[(s, m)] = len(verts)
            verts.append((s, m))
    edges, cells, per_slice = set(), [], []
    for s, sh in enumerate(shad):
        b0, b1, E, Tr = nerve_b1(len(sh), sh)
        per_slice.append((b0, b1))
        for i, j in E:
            edges.add((vid[(s, i)], vid[(s, j)]))
        for i, j, k in Tr:
            cells.append([vid[(s, i)], vid[(s, j)], vid[(s, k)]])
    inter = set()
    for s in range(len(slices) - 1):
        A, B_ = slices[s], slices[s + 1]
        if len(shad[s]) == 0 or len(shad[s + 1]) == 0:
            continue
        Ms = np.zeros((len(shad[s]), len(A)), np.float32)
        for m, sh in enumerate(shad[s]):
            Ms[m, list(sh)] = 1
        Mt = np.zeros((len(shad[s + 1]), len(B_)), np.float32)
        for m, sh in enumerate(shad[s + 1]):
            Mt[m, list(sh)] = 1
        link = (Ms @ R[np.ix_(A, B_)].astype(np.float32) @ Mt.T) > 0
        for i, j in zip(*np.nonzero(link)):
            u, v = vid[(s, i)], vid[(s + 1, j)]
            edges.add((min(u, v), max(u, v)))
            inter.add((min(u, v), max(u, v)))
    edges = sorted(edges)
    nbr = defaultdict(set)
    for i, j in edges:
        nbr[i].add(j)
        nbr[j].add(i)
    # inter-slice 2-cells with a WITNESS (local, Dowker-style): a triangle
    # {(s,m),(s,m'),(s+1,k)} needs one element a in S_m ∩ S_m' with a < b for
    # some b in S_k; {(s,m),(s+1,k),(s+1,k')} needs some a in S_m below an
    # element b in S_k ∩ S_k'.  Plain 3-cliques can wrap the circle once linked
    # shadows reach ~1/3 of the circumference (Rips-type filling).
    for s in range(len(slices) - 1):
        A, B_ = slices[s], slices[s + 1]
        if not shad[s] or not shad[s + 1]:
            continue
        Rab = R[np.ix_(A, B_)]
        up = [np.flatnonzero(Rab[a]) for a in range(len(A))]          # B-indices above a
        inB = defaultdict(list)
        for k, sh in enumerate(shad[s + 1]):
            for b in sh:
                inB[b].append(k)
        inA = defaultdict(list)
        for m_, sh in enumerate(shad[s]):
            for a in sh:
                inA[a].append(m_)
        for a in range(len(A)):
            ms = inA.get(a, [])
            if not ms:
                continue
            ks = set()
            for b in up[a]:
                kb = inB.get(b, [])
                ks.update(kb)
                for i1 in range(len(kb)):          # two upper shadows sharing b
                    for i2 in range(i1 + 1, len(kb)):
                        for m_ in ms:
                            cells.append(sorted((vid[(s, m_)], vid[(s + 1, kb[i1])], vid[(s + 1, kb[i2])])))
            for i1 in range(len(ms)):              # two lower shadows sharing a
                for i2 in range(i1 + 1, len(ms)):
                    for k in ks:
                        cells.append(sorted((vid[(s, ms[i1])], vid[(s, ms[i2])], vid[(s + 1, k)])))
    cells = [list(c) for c in {tuple(c) for c in cells}]
    return verts, edges, cells, nbr, per_slice


def window(rho=30000, ns=(40, 80, 160, 320), seeds=(0, 1)):
    ts = np.arange(0.1, T - 0.19, 0.05)
    for seed in seeds:
        rng = np.random.default_rng(seed)
        t, x, y, R = sprinkle21(rng, rho)
        print(f"seed={seed} rho={rho}: N={len(t)}", flush=True)
        for n in ns:
            slices, shad = build_slices(t, y, R, n, ts)
            verts, edges, cells, nbr, per_slice = complex_X(R, slices, shad)
            val, nfree, rank, _, conn, Cm = oc.cocycle(len(verts), edges, cells, nbr)
            print(f"  n={n:4d}: |A| per slice ~{int(np.mean([len(a) for a in slices]))}, shadows per slice "
                  f"~{np.mean([len(s) for s in shad]):.1f}; per-slice nerve (b0,b1): {dict(Counter(per_slice))};"
                  f" X: {len(verts)} vertices, {len(edges)} edges, {len(cells)} cells, connected={conn},"
                  f" dim H^1(X) = {nfree - rank}", flush=True)


def links_packed(R):
    P = np.packbits(R, axis=1, bitorder="little")
    N = len(R)
    out_i, out_j = [], []
    for i in range(N):
        S = np.flatnonzero(R[i])
        if len(S) == 0:
            continue
        cover = np.unpackbits(np.bitwise_or.reduce(P[S], axis=0), bitorder="little")[:N].astype(bool)
        L = R[i] & ~cover
        js = np.flatnonzero(L)
        out_i.append(np.full(len(js), i)); out_j.append(js)
    return np.concatenate(out_i), np.concatenate(out_j)


def circ_mean(th):
    return np.mod(np.angle(np.exp(2j * np.pi * np.asarray(th)).mean()) / (2 * np.pi), 1.0)


def run(rho=30000, n=160, seeds=(0, 1), B=4, dmax=0.25, S=1):
    ts = np.arange(0.1, T - 0.19, 0.05)
    for seed in seeds:
        rng = np.random.default_rng(seed)
        t, x, y, R = sprinkle21(rng, rho)
        N = len(t)
        slices, shad = build_slices(t, y, R, n, ts)
        verts, edges, cells, nbr, per_slice = complex_X(R, slices, shad)
        val, nfree, rank, _, conn, Cm = oc.cocycle(len(verts), edges, cells, nbr)
        h1 = nfree - rank
        print(f"\n=== 2+1 seed={seed} rho={rho} n={n}: N={N}, slices={len(slices)}, per-slice nerve "
              f"{dict(Counter(per_slice))}, dim H^1(X)={h1}", flush=True)
        if h1 != 1:
            continue
        # harmonic circular coordinate on shadow vertices
        g = np.array([1, 1]) if nfree == 1 else None
        if g is None:
            _, sv, Vt = np.linalg.svd(Cm[:, 1:].astype(float))
            gg = Vt[-1] / np.min(np.abs(Vt[-1][np.abs(Vt[-1]) > 1e-6]))
            g = np.concatenate([[1], np.round(gg).astype(int)])
        w = np.array([np.pad(val[e], (0, 1 + nfree - len(val[e]))) @ g for e in edges], float)
        E = len(edges)
        D = coo_matrix((np.tile([-1.0, 1.0], E), (np.repeat(np.arange(E), 2), np.array(edges).ravel())),
                       shape=(E, len(verts))).tocsr()
        f = lsqr(D, -w, atol=1e-12, btol=1e-12, iter_lim=50000)[0]
        thv = np.mod(f, 1.0)
        # down to slice elements, then off-slice elements
        theta = np.full(N, np.nan)
        sidx = np.full(N, -1)
        vid = {v: k for k, v in enumerate(verts)}
        for s, (A, sh) in enumerate(zip(slices, shad)):
            acc = defaultdict(list)
            for m, sset in enumerate(sh):
                for a in sset:
                    acc[a].append(thv[vid[(s, m)]])
            for a, ths in acc.items():
                theta[A[a]] = circ_mean(ths)
                sidx[A[a]] = s
        nsl = len(slices)
        mem = [A[~np.isnan(theta[A])] for A in slices]
        for v in range(N):
            if not np.isnan(theta[v]):
                continue
            for s in range(nsl - 1, -1, -1):
                mm = R[mem[s], v]
                if mm.any():
                    theta[v], sidx[v] = circ_mean(theta[mem[s][mm]]), s
                    break
            else:
                mm = R[v, mem[0]]
                if mm.any():
                    theta[v], sidx[v] = circ_mean(theta[mem[0][mm]]), 0
        ok = ~np.isnan(theta)
        # theta distortion vs coordinate (diagnostic only)
        for sg in (1, -1):
            off = np.angle(np.exp(2j * np.pi * (theta[ok] - sg * x[ok]))).mean() / (2 * np.pi)
            err = np.abs(np.angle(np.exp(2j * np.pi * (theta[ok] - sg * x[ok] - off))) / (2 * np.pi))
            if np.median(err) < 0.2:
                print(f"  theta vs coordinate (orientation {sg:+d}): |err| median {np.median(err):.3f}, 99% {np.quantile(err, .99):.3f}, max {err.max():.3f}")
        li, lj = links_packed(R)
        keep = ok[li] & ok[lj] & (np.abs(sidx[li] - sidx[lj]) <= B)
        li, lj = li[keep], lj[keep]
        jg = np.round(theta[li] - theta[lj]).astype(int)
        keep = np.abs(theta[lj] + jg - theta[li]) <= dmax
        gi, gj, jgen = li[keep], lj[keep], jg[keep]
        # gauge match against coordinates (diagnostic)
        cgen = np.round(x[gi] - x[gj]).astype(int)
        best = None
        for sg in (1, -1):
            adj = defaultdict(list)
            for a, b, w_, c_ in zip(gi, gj, jgen, cgen):
                h = int(w_ - sg * c_)
                adj[int(a)].append((int(b), h)); adj[int(b)].append((int(a), -h))
            delta = {}
            for root in np.flatnonzero(ok):
                root = int(root)
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
            bad = sum(1 for a, b, w_, c_ in zip(gi, gj, jgen, cgen) if w_ - sg * c_ != delta[int(b)] - delta[int(a)])
            if best is None or bad < best[0]:
                best = (bad, sg, delta)
        bad, sgn, delta = best
        print(f"  generators {len(gi)} of {len(keep)} span-eligible links; gauge-mismatched {bad}; orientation {sgn:+d}", flush=True)
        # closure on sheets -S..S
        W = 2 * S + 1
        succ = defaultdict(list)
        for a, b, k in zip(gi, gj, jgen):
            succ[int(a)].append((int(b), int(k)))
        reach = {}
        for u in np.argsort(t)[::-1]:
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
        tab = Counter(); taub = defaultdict(Counter); two = [0, 0, 0]; imgs = Counter()
        srcs = np.flatnonzero(ok & (y > 0.2) & (y < Y - 0.2))
        js = np.arange(-S, S + 1)
        for u in srcs:
            r = reach.get((int(u), 0), 0)
            bits = (np.unpackbits(np.frombuffer(r.to_bytes(nb, "little"), np.uint8), bitorder="little")[: N * W]
                    .reshape(N, W).astype(bool)) if r else np.zeros((N, W), bool)
            vs = np.flatnonzero(ok & (t > t[u]))
            ku = sgn * (0 - dl[u])
            kv = sgn * (js[None, :] - dl[vs][:, None])
            dxx = x[vs][:, None] + kv - x[u] - ku
            dyy = (y[vs] - y[u])[:, None]
            dt = (t[vs] - t[u])[:, None]
            sp = np.sqrt(dxx**2 + dyy**2)
            coord = dt > sp
            o = bits[vs]
            tab["TP"] += int((o & coord).sum()); tab["FP"] += int((o & ~coord).sum()); tab["FN"] += int((~o & coord).sum())
            tau = np.sqrt(np.maximum(dt**2 - sp**2, 0))
            tb = np.minimum((tau / 0.05).astype(int), 6)
            for b_ in range(7):
                m_ = coord & (tb == b_)
                taub[b_]["TP"] += int((o & m_).sum()); taub[b_]["FN"] += int((~o & m_).sum())
            base = R[u, vs]
            nc, no = coord[base].sum(axis=1), (o & coord)[base].sum(axis=1)
            m2 = nc == 2
            two[0] += int(m2.sum()); two[1] += int((no[m2] < 2).sum()); two[2] += int((2 - no[m2]).sum())
            for a_, b_ in zip(nc, (o[base]).sum(axis=1)):
                imgs[(int(a_), int(b_))] += 1
        fnr = tab["FN"] / max(tab["FN"] + tab["TP"], 1)
        print(f"  entries (sources in central y band): {dict(tab)}; FP={tab['FP']}, FN rate {fnr:.2%}")
        print("  FN by tau: " + ", ".join(
            f"[{b*0.05:.2f},{(b+1)*0.05:.2f}){'' if b < 6 else '+'} {taub[b]['FN']/max(taub[b]['FN']+taub[b]['TP'],1):.1%}" for b in range(7)))
        print(f"  two-image base pairs: {two[0]}; pairs missing a sheet {two[1]/max(two[0],1):.2%}; sheets missed {two[2]/max(2*two[0],1):.2%}")
        print(f"  (continuum #images, order #sheets) -> count: {dict(sorted(imgs.items()))}", flush=True)


if __name__ == "__main__":
    {"window": window, "run": run}[sys.argv[1] if len(sys.argv) > 1 else "window"]()
