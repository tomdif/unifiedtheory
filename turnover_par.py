"""TURNOVER CHECK v4 (parallel): identical mathematics to
turnover_check2.py v3 (ellipsoid law NSTART=16, same class keys,
same spill-reduce final level), reorganized for wall-clock:
per level, PASS A scans parents in parallel to collect the distinct
gap systems, the pool solves unsolved systems in parallel (each
solve is per-key deterministic, so parallelism cannot change any
result), PASS B emits children in parallel with the complete cache.
Validation: tex ladder must match the serial v3 run to reference-
noise (sprinkling refs here are seeded rng(999), so internal
consistency is exact and cross-run agreement is ~1e-3).
Workers inherit state via fork + copy-on-write; only slice indices
are passed."""
import numpy as np, math, sys, time, resource, struct, os
import multiprocessing as mp
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)
def rss(): return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/2**30
exec(open('selection_and_action.py').read().split('if MODE == "A":')[0])
from law_ellipsoid import make_law_ell
NMAX = int(os.environ.get("NMAX_OVERRIDE", 11))
NW = int(os.environ.get("NW_OVERRIDE", 6))
ARANGE = {n: np.arange(1 << n, dtype=np.int64) for n in range(1, NMAX)}
W = (1,-3,2); PHIF = 0.625
LAW = make_law_ell(PHIF*math.pi, NSTART=16)
warr = np.zeros(NMAX+2, dtype=np.int64)
for k in range(3): warr[k] = W[k]

def sprink(n, T=6000):
    r2 = np.random.default_rng(999)
    rs=[]; abs_=np.zeros(3)
    for _ in range(T):
        u=r2.random(n); v=r2.random(n)
        idx=np.argsort(u); v=v[idx]
        bel=[0]*n
        for i in range(n):
            for j in range(i):
                if v[j]<v[i]: bel[i] |= 1<<j
        rs.append(sum(bin(b).count("1") for b in bel)/(n*(n-1)/2))
        above=[0]*n
        for x in range(n):
            m=bel[x]
            while m:
                y=(m&-m).bit_length()-1; above[y]|=1<<x; m&=m-1
        for x in range(n):
            m=bel[x]
            while m:
                y=(m&-m).bit_length()-1
                kk=bin(above[y]&bel[x]).count("1")
                if kk<3: abs_[kk]+=1
                m&=m-1
    return float(np.mean(rs)), abs_/T/n
SPR = {n: sprink(n) for n in range(min(8, NMAX), NMAX+1)}
TEX = {}
for n in SPR: log(f"sprinkling n={n}: ab={np.round(SPR[n][1],3)}")

def pack_below(bel): return struct.pack(f"<{len(bel)}H", *bel)
def unpack_below(b, n): return list(struct.unpack(f"<{n}H", b))

def combinatorics(bel, n):
    """Everything up to (but excluding) the law call."""
    above = [0]*n
    for x in range(n):
        m = bel[x]
        while m:
            y = (m & -m).bit_length()-1
            above[y] |= 1 << x; m &= m-1
    masks = ARANGE[n]; okm = np.ones(masks.shape[0], dtype=bool)
    for x in range(n):
        bx = bel[x]
        if bx == 0: continue
        okm &= ~(((masks>>x)&1==1)&((masks&bx)!=bx))
    dlist = masks[okm]
    nc = dlist.shape[0]
    g = np.ones(nc, dtype=np.int64)
    h0 = np.zeros(nc, dtype=np.int64); h1 = np.zeros(nc, dtype=np.int64); h2 = np.zeros(nc, dtype=np.int64)
    bits = ((dlist[:, None] >> np.arange(n)) & 1).astype(bool)
    for d in range(n):
        sel = bits[:, d]
        if not sel.any(): continue
        kv = popcount(dlist[sel] & np.int64(above[d])).astype(np.int64)
        g[sel] -= warr[np.minimum(kv, 2)]
        h0[sel] += (kv == 0); h1[sel] += (kv == 1); h2[sel] += (kv == 2)
    gc = {}
    for gg in g.tolist(): gc[gg] = gc.get(gg, 0)+1
    return above, dlist, bits, g, h0, h1, h2, gc

def child_invariants(bel, n, above, dlist, bits, g, h0, R):
    nc = dlist.shape[0]
    indeg = np.array([bin(b).count("1") for b in bel])
    outdeg = np.array([bin(a).count("1") for a in above])
    hgt = np.ones(n, dtype=np.int64)
    for x in sorted(range(n), key=lambda x: bin(bel[x]).count("1")):
        m = bel[x]; best = 0
        while m:
            y = (m&-m).bit_length()-1
            if hgt[y] > best: best = hgt[y]
            m &= m-1
        hgt[x] = best + 1
    popD = bits.sum(axis=1)
    out_ch = outdeg[None, :] + bits
    hnew = 1 + (hgt[None, :] * bits).max(axis=1)
    enc_old = (np.broadcast_to(indeg, (nc, n)) * 4096
               + out_ch * 64 + np.broadcast_to(hgt, (nc, n)))
    enc_new = (popD * 4096 + 0 * 64 + hnew)[:, None]
    enc = np.sort(np.concatenate([enc_old, enc_new], axis=1), axis=1)
    Rn = R + popD
    return enc, Rn

# globals shared with fork workers
STATE_VALS = None   # list of value-lists at the current level
CUR_N = None
CACHE = {}          # gc key tuple -> weights dict or None

def gckey(gc): return tuple(sorted(gc.items()))

def scan_worker(args):
    lo, hi = args
    keys = set()
    n = CUR_N
    for i in range(lo, hi):
        A, P, belb, N0, N1, N2, R, ACT = STATE_VALS[i]
        bel = unpack_below(belb, n)
        *_, gc = combinatorics(bel, n)
        keys.add(gckey(gc))
    return keys

def solve_worker(key):
    return key, LAW(dict(key))

def emit_dict_worker(args):
    lo, hi = args
    n = CUR_N
    new = {}
    for i in range(lo, hi):
        A, P, belb, N0, N1, N2, R, ACT = STATE_VALS[i]
        bel = unpack_below(belb, n)
        above, dlist, bits, g, h0, h1, h2, gc = combinatorics(bel, n)
        lw = CACHE[gckey(gc)]
        if lw is None: continue
        p = np.array([lw[gg] for gg in g.tolist()]); p = np.maximum(p, 0)
        s = p.sum()
        if s <= 0: continue
        p = p / s
        enc, Rn = child_invariants(bel, n, above, dlist, bits, g, h0, R)
        plist = p.tolist(); glist = g.tolist()
        for j in range(dlist.shape[0]):
            pp = plist[j]
            if pp < 1e-13: continue
            gg = glist[j]
            ckey = (Rn[j].tobytes() + np.int64(ACT + gg).tobytes()
                    + np.int64(round(N0 + float(h0[j]))).tobytes() + enc[j].tobytes())
            a = A * math.sqrt(pp) * complex(math.cos(PHIF*math.pi*gg), math.sin(PHIF*math.pi*gg))
            pr = P * pp
            e = new.get(ckey)
            if e is not None:
                e[0] += a; e[1] += pr
            else:
                cb = bel + [int(dlist[j])]
                new[ckey] = [a, pr, pack_below(cb),
                             N0 + float(h0[j]), N1 + float(h1[j]), N2 + float(h2[j]), int(Rn[j]),
                             ACT + gg]
    return new

def emit_spill_worker(args):
    lo, hi, shard = args
    n = CUR_N
    KW = n + 4
    Ks = []; Vs = []
    for i in range(lo, hi):
        A, P, belb, N0, N1, N2, R, ACT = STATE_VALS[i]
        bel = unpack_below(belb, n)
        above, dlist, bits, g, h0, h1, h2, gc = combinatorics(bel, n)
        lw = CACHE[gckey(gc)]
        if lw is None: continue
        p = np.array([lw[gg] for gg in g.tolist()]); p = np.maximum(p, 0)
        s = p.sum()
        if s <= 0: continue
        p = p / s
        enc, Rn = child_invariants(bel, n, above, dlist, bits, g, h0, R)
        jj = np.flatnonzero(p >= 1e-13)
        if jj.size == 0: continue
        gg = g[jj]; pp = p[jj]
        Krow = np.empty((jj.size, KW), np.uint16)
        Krow[:, 0] = Rn[jj]
        Krow[:, 1] = (ACT + gg + 512)
        Krow[:, 2] = np.round(N0 + h0[jj]).astype(np.int64)
        Krow[:, 3:] = enc[jj]
        a = A * np.sqrt(pp) * np.exp(1j * PHIF * math.pi * gg)
        Vrow = np.stack([a.real, a.imag, P * pp,
                         N1 + h1[jj].astype(float), N2 + h2[jj].astype(float)], axis=1)
        Ks.append(Krow); Vs.append(Vrow)
    K = np.concatenate(Ks) if Ks else np.empty((0, KW), np.uint16)
    V = np.concatenate(Vs) if Vs else np.empty((0, 5), np.float64)
    np.save(f"{SPILL}/K_{shard}.npy", K); np.save(f"{SPILL}/V_{shard}.npy", V)
    return shard, K.shape[0]

SPILL = os.path.join(os.environ.get("TMPDIR", "/tmp"), "turnover_spill")
os.makedirs(SPILL, exist_ok=True)

def slices(N, k):
    step = (N + k - 1)//k
    return [(i, min(i+step, N)) for i in range(0, N, step)]

def solve_missing(pool, keysets):
    allk = set().union(*keysets) if isinstance(keysets, list) else keysets
    missing = [k for k in allk if k not in CACHE]
    if missing:
        for key, out in pool.imap_unordered(solve_worker, missing, chunksize=4):
            CACHE[key] = out
    return len(missing)

def observables(nn, mu_w, P_w, N0a, N1a, N2a, Ra):
    r_s, ab_s = SPR[nn]
    mu_tot = mu_w.sum(); P_tot = P_w.sum()
    ab = np.stack([N0a, N1a, N2a], axis=1) / nn
    t_ = np.sqrt(((ab - np.asarray(ab_s)[None, :])**2).sum(axis=1))
    r_ = Ra / (nn*(nn-1)/2)
    return (float((mu_w/mu_tot * t_).sum()), float((P_w/P_tot * t_).sum()),
            float((mu_w/mu_tot * r_).sum()))

if __name__ == "__main__":
    mp.set_start_method("fork")
    states = {b"root": [1+0j, 1.0, pack_below([0]), 0.0, 0.0, 0.0, 0, 0]}
    pool = mp.Pool(NW)
    for n in range(1, NMAX-1):
        t0 = time.time()
        STATE_VALS = list(states.values()); CUR_N = n
        # re-fork the pool so workers see the new level's globals
        pool.close(); pool.join(); pool = mp.Pool(NW)
        sl = slices(len(STATE_VALS), NW*4)
        keysets = pool.map(scan_worker, sl)
        nsolved = solve_missing(pool, keysets)
        # cache updated in master; re-fork so emit workers see it
        pool.close(); pool.join(); pool = mp.Pool(NW)
        dicts = pool.map(emit_dict_worker, sl)
        new = dicts[0]
        for d in dicts[1:]:
            for ckey, e in d.items():
                ee = new.get(ckey)
                if ee is not None:
                    ee[0] += e[0]; ee[1] += e[1]
                else:
                    new[ckey] = e
        states = new
        nn = n+1
        log(f"level {nn}: {len(states)} classes  (solved {nsolved} new gc; {time.time()-t0:.0f}s)  rss={rss():.1f}GB")
        if nn in (8, 9, 10):
            vals = list(states.values())
            mu_w = np.array([abs(e[0])**2 for e in vals]); P_w = np.array([e[1] for e in vals])
            N0a = np.array([e[3] for e in vals]); N1a = np.array([e[4] for e in vals])
            N2a = np.array([e[5] for e in vals]); Ra = np.array([float(e[6]) for e in vals])
            tMu, tP, rMu = observables(nn, mu_w, P_w, N0a, N1a, N2a, Ra)
            log(f"  n={nn}: tex_mu={tMu:.4f}  tex_P={tP:.4f}  r_mu={rMu:.4f}")
            TEX[nn] = tMu
    # final level 10->11: spill path
    n = NMAX-1; CUR_N = n
    t0 = time.time()
    STATE_VALS = list(states.values())
    del states
    pool.close(); pool.join(); pool = mp.Pool(NW)
    sl = slices(len(STATE_VALS), NW*6)
    log(f"final level: scanning {len(STATE_VALS)} parents in {len(sl)} slices")
    keysets = pool.map(scan_worker, sl)
    nsolved = solve_missing(pool, keysets)
    log(f"final level: solved {nsolved} new gc systems  ({time.time()-t0:.0f}s)  rss={rss():.1f}GB")
    pool.close(); pool.join(); pool = mp.Pool(NW)
    args = [(lo, hi, i) for i, (lo, hi) in enumerate(sl)]
    tot = 0
    for shard, cnt in pool.imap_unordered(emit_spill_worker, args):
        tot += cnt
        log(f"  shard {shard}: {cnt} rows (total {tot})")
    pool.close(); pool.join()
    # master sort-reduce over all shards
    KW = n + 4
    K_m = None; V_m = None
    for i in range(len(sl)):
        K = np.load(f"{SPILL}/K_{i}.npy"); V = np.load(f"{SPILL}/V_{i}.npy")
        if K_m is not None:
            K = np.concatenate([K_m, K]); V = np.concatenate([V_m, V])
        Kv = np.ascontiguousarray(K).view([('b', f'V{2*KW}')]).ravel()
        order = np.argsort(Kv, kind='stable')
        Kv = Kv[order]; K = K[order]; V = V[order]
        newgrp = np.empty(Kv.shape[0], bool); newgrp[0] = True
        newgrp[1:] = Kv[1:] != Kv[:-1]
        first = np.flatnonzero(newgrp)
        gid = np.cumsum(newgrp) - 1
        ng = first.shape[0]
        Vm = np.empty((ng, 5))
        for c in (0, 1, 2):
            Vm[:, c] = np.bincount(gid, weights=V[:, c], minlength=ng)
        Vm[:, 3] = V[first, 3]; Vm[:, 4] = V[first, 4]
        K_m = K[first].copy(); V_m = Vm
        log(f"  reduce {i+1}/{len(sl)}: master {K_m.shape[0]} classes  rss={rss():.1f}GB")
    nn = NMAX
    log(f"level {nn}: {K_m.shape[0]} classes  ({time.time()-t0:.0f}s)")
    mu = V_m[:, 0]**2 + V_m[:, 1]**2
    tMu, tP, rMu = observables(nn, mu, V_m[:, 2], K_m[:, 2].astype(float), V_m[:, 3], V_m[:, 4], K_m[:, 0].astype(float))
    log(f"  n={nn}: tex_mu={tMu:.4f}  tex_P={tP:.4f}  r_mu={rMu:.4f}")
    wts = np.sort(mu)[::-1]
    c = np.cumsum(wts)/mu.sum()
    k95 = int(np.searchsorted(c, 0.95))+1; k999 = int(np.searchsorted(c, 0.999))+1
    log(f"  mass concentration: 95% in {k95} classes, 99.9% in {k999}")
    TEX[nn] = tMu
    if NMAX == 11:
        lad = [TEX[k] for k in (8,9,10,11)]
        incs = [lad[i+1]-lad[i] for i in range(3)]
        log(f"  CORRECTED LADDER tex_mu(8..11) = {['%.4f'%v for v in lad]}")
        log(f"  increments: {['%+.4f'%v for v in incs]}")
    log("DONE-TURN-PAR")
