"""Build the Z-cover of a sprinkled cylinder causal set from the order, locally.

1. A stack of order-chosen maximal antichains A_1..A_m (levels of |J-(x)|,
   greedily extended; ~0.05 apart in time).
2. 2-complex X on the union of slice elements:
     edges     = Dowker (common-shadow) edges inside each slice
               + relations a < b between ADJACENT slices;
     triangles = all 3-cliques of that graph (all short).
3. Integral cocycle on X by propagating triangle flatness from a spanning tree,
   carrying values as integer vectors over free variables: every forced free
   variable is one dimension of H^1(X).  Expect exactly one; set it to 1.
4. Lift adjacent-slice relations: (a, i) < (b, i + w(a, b)); take the
   transitive closure.  This is the order-built cover (restricted to slices).
5. Compare with the coordinate cover, entry by entry, after one gauge match:
   w - s*c = coboundary (c = coordinate sheet change of a short edge).
   FP (order relates, coordinates do not) must be 0 if the gauge match holds.
   FN = coordinate relations with no short-step decomposition through slices.
   Also: #sheets j with (u,0) < (v,j) = order-derived image count.
Coordinates are used only for building slices' levels and for step 5.

Usage: python3.11 scripts/ab_order_cover.py
"""
import numpy as np
from collections import deque, Counter, defaultdict
from ab_slicing_and_images import sprinkle, maximal_slice
from ab_chain_pair_holonomy import shadows


def past_level(rho, t):
    return rho * (t * t if t <= 0.5 else t - 0.25)


def build(seed=0, rho=3000, T=1.4, n=12, ts=None):
    rng = np.random.default_rng(seed)
    t, x, dx, R = sprinkle(rng, rho, T)
    past = R.sum(axis=0)
    ts = ts if ts is not None else np.arange(0.1, T - 0.08, 0.05)
    slice_of = {}
    slices = []
    for s, tt in enumerate(ts):
        A, _, _ = maximal_slice(R, past, past_level(rho, tt))
        A = np.array([a for a in A if a not in slice_of])
        for a in A:
            slice_of[a] = s
        slices.append(A)
    V = np.array(sorted(slice_of))
    vid = {v: k for k, v in enumerate(V)}
    sl = np.array([slice_of[v] for v in V])
    edges = set()
    for s, A in enumerate(slices):
        if len(A) < 3:
            continue
        for sh in shadows(R, A, n):
            idx = sorted(vid[A[k]] for k in sh)
            for i in range(len(idx)):
                for j in range(i + 1, len(idx)):
                    edges.add((idx[i], idx[j]))
    RV = R[np.ix_(V, V)]
    inter = []
    for i in range(len(V)):
        for j in np.flatnonzero(RV[i]):
            if abs(sl[i] - sl[j]) == 1:
                edges.add((min(i, j), max(i, j)))
                inter.append((i, j))  # oriented i < j in the order
    edges = sorted(edges)
    return t, x, R, V, sl, edges, inter


def cells_of(edges, inter, sl):
    """2-cells: all 3-cliques, plus squares a~a' (slice s), a<b, a'<b', b~b' (slice s+1)."""
    nbr = defaultdict(set)
    for i, j in edges:
        nbr[i].add(j)
        nbr[j].add(i)
    cells = [[i, j, k] for i, j in edges for k in nbr[i] & nbr[j] if k > j]
    fut = defaultdict(set)
    for i, j in inter:
        if sl[j] == sl[i] + 1:
            fut[i].add(j)
    for a, a2 in edges:
        if sl[a] != sl[a2]:
            continue
        for b in fut[a] - fut[a2]:
            for b2 in fut[a2] - fut[a]:
                if b2 in nbr[b] and sl[b2] == sl[b]:
                    cells.append([a, a2, b2, b])
    return cells, nbr


def cocycle(nV, edges, cells, nbr):
    val = {}
    seen = {0}
    q = deque([0])
    while q:  # BFS spanning tree, gauge 0
        u = q.popleft()
        for v in nbr[u]:
            if v not in seen:
                seen.add(v)
                val[(min(u, v), max(u, v))] = np.zeros(1, int)
                q.append(v)
    conn = len(seen) == nV
    nfree = 0
    constraints = []

    def get(u, v):
        e = (min(u, v), max(u, v))
        x = val.get(e)
        if x is None:
            return None
        x = np.pad(x, (0, 1 + nfree - len(x)))
        return x if u < v else -x

    work = deque(range(len(cells)))
    while True:
        progressed = True
        while progressed:
            progressed = False
            for _ in range(len(work)):
                ci = work.popleft()
                cyc = cells[ci]
                steps = list(zip(cyc, cyc[1:] + cyc[:1]))
                vals = [get(u, v) for u, v in steps]
                miss = [k for k, x in enumerate(vals) if x is None]
                if not miss:
                    r = sum(vals)
                    if np.any(r):
                        constraints.append(r)
                    continue
                if len(miss) == 1:
                    u, v = steps[miss[0]]
                    rest = sum(x for x in vals if x is not None)
                    x = -rest  # W(u,v) = -sum(others)
                    val[(min(u, v), max(u, v))] = x if u < v else -x
                    progressed = True
                    continue
                work.append(ci)
        unknown = [e for e in edges if e not in val]
        if not unknown:
            break
        nfree += 1
        x = np.zeros(1 + nfree, int)
        x[nfree] = 1
        val[unknown[0]] = x
    Cm = np.array([np.pad(r, (0, 1 + nfree - len(r))) for r in constraints]) if constraints else np.zeros((0, 1 + nfree), int)
    rank = np.linalg.matrix_rank(Cm[:, 1:].astype(float)) if len(Cm) else 0
    if len(Cm) and np.any(Cm[:, 0]):
        print("  WARNING: inhomogeneous constraint (inconsistent gauge)")
    return val, nfree, rank, cells, conn, Cm


def main(seed=0, rho=3000, n=25):
    t, x, R, V, sl, edges, inter = build(seed, rho, n=n)
    cells, nbr = cells_of(edges, inter, sl)
    val, nfree, rank, tris, conn, Cm = cocycle(len(V), edges, cells, nbr)
    h1 = nfree - rank
    print(f"seed={seed} rho={rho} n={n}: slices={sl.max()+1}, |V|={len(V)}, edges={len(edges)}"
          f" (inter-slice {len(inter)}), 2-cells={len(tris)} (squares {sum(len(c)==4 for c in tris)}), connected={conn};"
          f" free vars {nfree}, constraint rank {rank} -> dim H^1(X) = {h1}")
    if h1 != 1:
        return
    # pick the solution g = generator; if nfree > 1, solve constraints for others
    if nfree == 1:
        g = np.array([1, 1])
    else:
        # one-dim solution space of Cm[:,1:] g = 0; take the integral generator
        _, sv, Vt = np.linalg.svd(Cm[:, 1:].astype(float))
        gg = Vt[-1]
        gg = gg / np.min(np.abs(gg[np.abs(gg) > 1e-6]))
        assert np.allclose(gg, np.round(gg), atol=1e-6)
        g = np.concatenate([[1], np.round(gg).astype(int)])
    w = {e: int(np.pad(v, (0, 1 + nfree - len(v))) @ g) for e, v in val.items()}
    W = lambda i, j: w[(i, j)] if i < j else -w[(j, i)]
    # coordinate sheet change of a short edge: k with x_j + k - x_i in [-0.5, 0.5)
    X = x[V]
    c = lambda i, j: int(np.round(X[i] - X[j]))
    # gauge match: w - s*c should be a coboundary
    best = None
    for s in (1, -1):
        delta = {0: 0}
        q = deque([0])
        nbr = defaultdict(set)
        for i, j in edges:
            nbr[i].add(j)
            nbr[j].add(i)
        while q:
            u = q.popleft()
            for v in nbr[u]:
                if v not in delta:
                    delta[v] = delta[u] + W(u, v) - s * c(u, v)
                    q.append(v)
        bad = sum(1 for i, j in edges if W(i, j) - s * c(i, j) != delta[j] - delta[i])
        if best is None or bad < best[0]:
            best = (bad, s, delta)
    bad, s, delta = best
    print(f"  edge-level gauge match: orientation s={s:+d}, mismatched edges {bad} of {len(edges)}")
    # lifted transitive closure over sheets
    S = 3
    nV = len(V)
    order = np.argsort(t[V])
    succ = defaultdict(list)
    for i, j in inter:
        succ[i].append(j)
    reach = {}
    node = lambda v, k: int(v) * (2 * S + 1) + (k + S)
    for u in order[::-1]:
        for k in range(-S, S + 1):
            r = 0
            for v in succ[u]:
                kk = k + W(u, v)
                if -S <= kk <= S:
                    r |= (1 << node(v, kk)) | reach.get((v, kk), 0)
            reach[(u, k)] = r
    # compare, entry by entry, for sources on sheet 0
    tab = Counter()
    imgs = Counter()
    taub = defaultdict(Counter)
    plateau = Counter()
    pred = defaultdict(list)
    for i, j in inter:
        pred[j].append(i)
    dead_frac = np.mean([(not succ[u]) for u in range(nV) if sl[u] < sl.max()])
    dead_in = np.mean([(not pred[u]) for u in range(nV) if sl[u] > 0])
    T_ = t[V]
    for u in range(nV):
        ku = s * (0 - delta[u])
        r = reach[(u, 0)]
        for v in range(nV):
            if sl[v] <= sl[u]:
                continue
            n_order = n_coord = 0
            for j in range(-S, S + 1):
                kv = s * (j - delta[v])
                coord = T_[v] - T_[u] > abs(X[v] + kv - X[u] - ku)
                order_rel = bool((r >> node(v, j)) & 1)
                outcome = ("TP" if coord else "FP") if order_rel else ("FN" if coord else "TN")
                tab[outcome] += 1
                if coord:
                    d = abs(X[v] + kv - X[u] - ku)
                    tau = np.sqrt((T_[v] - T_[u]) ** 2 - d * d)
                    tb = min(int(tau / 0.05), 6)
                    taub[(tb, sl[v] - sl[u] == 1)][outcome] += 1
                    if tb == 6:
                        dead = (not succ[u]) or (not pred[v])
                        plateau[(outcome, dead)] += 1
                n_order += order_rel
                n_coord += coord
            if R[V[u], V[v]]:
                imgs[(n_coord, n_order)] += 1
    print(f"  lifted causal matrix vs coordinate cover (sheets ±{S}): {dict(tab)}")
    fn_rate = tab["FN"] / max(tab["FN"] + tab["TP"], 1)
    print(f"  FP = {tab['FP']}, FN rate = {fn_rate:.2%}")
    print("  FN rate by proper time tau of the lifted pair (adjacent slices / further apart):")
    for tb in range(7):
        row = []
        for adj in (True, False):
            c_ = taub.get((tb, adj), Counter())
            tot = c_["TP"] + c_["FN"]
            row.append(f"{c_['FN']/tot:6.1%} of {tot:7d}" if tot else "      -          ")
        lab = f"[{tb*0.05:.2f},{(tb+1)*0.05:.2f})" if tb < 6 else ">=0.30     "
        print(f"    tau {lab}: adjacent {row[0]}   non-adjacent {row[1]}")
    print(f"  plateau check (tau>=0.3): elements with no generator up {dead_frac:.1%}, no generator down {dead_in:.1%}")
    for dd in (True, False):
        tp_, fn_ = plateau[("TP", dd)], plateau[("FN", dd)]
        print(f"    end without generator={dd}: FN {fn_} of {tp_+fn_} ({fn_/max(tp_+fn_,1):.1%})")
    print(f"  related base pairs: (continuum #images, order-cover #images) -> count: {dict(sorted(imgs.items()))}")
    return t, x, R, V, sl, inter, W, s, delta, tab


if __name__ == "__main__":
    for seed in (0, 1):
        main(seed)
