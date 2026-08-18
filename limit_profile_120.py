"""LIMIT PROFILE AT n=120 (registered 2026-08-17, open attack 1).
Hard ceiling of the two-limb machinery (LIMB=60 x 2).  Birth-frozen
prediction: the profile restricted to tops in birth quartile q at
size n matches the all-tops profile of a universe of size ~ q*n.
DECISIVE: the youngest-quartile tail - does d(k) descend cleanly
toward 2 inside the window (limit profile = manifold bulk), or
undershoot/plateau above?
READINGS: (i) CLEAN DESCENT: youngest-quartile d(k) approaches 2
from above through k~45-64 with crossing at ~4.5*sqrt(120)~49 =>
limit profile is manifold-like; (ii) PLATEAU >2 or undershoot <2
inside the window => UV elevation persists at all scales or
over-ordering is not confined; (iii) quartile prediction fails =>
birth-frozen model incomplete."""
import numpy as np, math, time
T0=time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)
from law_ellipsoid import make_law_ell
rng = np.random.default_rng(20260822)
law = make_law_ell(math.pi/4, NSTART=16, disk_cache="law_cache_pi4_16.pkl")
POP16 = np.array([bin(i).count("1") for i in range(1 << 16)], dtype=np.int64)
def popcount(arr):
    return (POP16[arr & 0xFFFF] + POP16[(arr >> 16) & 0xFFFF] +
            POP16[(arr >> 32) & 0xFFFF] + POP16[(arr >> 48) & 0x7FFF])
W2ARR = np.array([2, -4, 2, 0], dtype=np.int64)
LIMB = 60; LOWM = (1 << LIMB) - 1
NF = 112; IDEAL_CAP = 20_000_000
def grow(N):
    for attempt in range(6):
        below = [0]; above = [0]
        ids0 = np.array([0, 1], dtype=np.int64)
        ids1 = np.array([0, 0], dtype=np.int64)
        ok = True
        for n in range(1, N):
            gaps = np.ones(len(ids0), dtype=np.int64)
            for y in range(n):
                iy = ((ids0 >> y) & 1) == 1 if y < LIMB else ((ids1 >> (y - LIMB)) & 1) == 1
                if not iy.any(): continue
                A0 = np.int64(above[y] & LOWM); A1 = np.int64(above[y] >> LIMB)
                k = popcount(ids0 & A0) + popcount(ids1 & A1)
                gaps -= np.where(iy, W2ARR[np.minimum(k, 3)], 0)
            gu, inv = np.unique(gaps, return_inverse=True)
            gc = dict(zip(gu.tolist(), np.bincount(inv).tolist()))
            lw = law(gc)
            if lw is None:
                log(f"    attempt died: LAW WALL at step {n}")
                ok = False; break
            lw_arr = np.array([lw[g] for g in gu.tolist()])
            probs = np.maximum(lw_arr[inv], 0)
            s = probs.sum()
            if s <= 0: ok = False; break
            j = rng.choice(len(ids0), p=probs/s)
            D = int(ids0[j]) | (int(ids1[j]) << LIMB)
            D0 = np.int64(D & LOWM); D1 = np.int64(D >> LIMB)
            keep = ((ids0 & D0) == D0) & ((ids1 & D1) == D1)
            nb0 = np.int64(1 << n) if n < LIMB else np.int64(0)
            nb1 = np.int64(0) if n < LIMB else np.int64(1 << (n - LIMB))
            ids0 = np.concatenate([ids0, ids0[keep] | nb0])
            ids1 = np.concatenate([ids1, ids1[keep] | nb1])
            if len(ids0) > IDEAL_CAP:
                log(f"    attempt died: CAP at step {n} ({len(ids0)} ideals)")
                ok = False; break
            below.append(D); above.append(0)
            mm = D
            while mm:
                d = (mm & -mm).bit_length()-1; above[d] |= 1 << n; mm &= mm-1
        if ok: break
    else:
        return None
    R = np.zeros((N, N), dtype=bool)
    for x in range(N):
        mm = below[x]
        while mm:
            y = (mm & -mm).bit_length()-1; R[y, x] = True; mm &= mm-1
    return R
MM_D = np.array([1.5, 2, 3, 4, 5, 6, 8, 10], float)
MM_F = np.array([0.75, 0.5000, 0.2296, 0.0994, 0.0417, 0.0170, 0.00287, 0.000496])
_ORD = np.argsort(-np.log(MM_F)); _XP = (-np.log(MM_F))[_ORD]; _FP = MM_D[_ORD]
def d_from_f(f):
    if f is None or f <= 0: return float("nan")
    return float(np.interp(-math.log(f), _XP, _FP))
QUART = [(0, 28), (28, 56), (56, 84), (84, 112)]
def profiles(R, N):
    ps = [dict() for _ in range(4)]; pall = {}
    got = 0; tries = 0
    while got < 4000 and tries < 500000:
        tries += 1
        x, y = rng.integers(N), rng.integers(N)
        if not R[x, y]:
            x, y = y, x
            if not R[x, y]: continue
        inter = np.nonzero(R[x, :] & R[:, y])[0]
        k = len(inter)
        if k < 4: continue
        sub = R[np.ix_(inter, inter)]
        f = sub.sum()/(k*(k-1)/2)
        b = int(round(2*math.log2(k)))
        pall.setdefault(b, []).append(f)
        for qi, (lo, hi) in enumerate(QUART):
            if lo <= y < hi: ps[qi].setdefault(b, []).append(f); break
        got += 1
    return pall, ps
M = 5
import os
grown = []
for i in range(M):
    ck = f"ckpt_limit112_{i}.npy"
    if os.path.exists(ck):
        grown.append(np.load(ck)); log(f"{i+1}/{M}: loaded checkpoint"); continue
    R = grow(NF)
    if R is not None:
        grown.append(R); np.save(ck, R)
    law.persist()
    log(f"{i+1}/{M} attempted, {len(grown)} grown")
PA = {}; PQ = [dict() for _ in range(4)]
for R in grown:
    a, qs = profiles(R, NF)
    for b, v in a.items(): PA.setdefault(b, []).extend(v)
    for qi in range(4):
        for b, v in qs[qi].items(): PQ[qi].setdefault(b, []).extend(v)
def show(P, name):
    parts = []; ks = []; ds = []
    for b in sorted(P):
        fs = P[b]
        if len(fs) < 25: continue
        kmid = 2**(b/2); d = d_from_f(float(np.mean(fs)))
        ks.append(kmid); ds.append(d)
        parts.append(f"k{kmid:.0f}:{d:.2f}")
    kx = None
    for i in range(len(ks)-1):
        if ds[i] >= 2.0 > ds[i+1]:
            t = (ds[i]-2.0)/(ds[i]-ds[i+1]); kx = ks[i]*(ks[i+1]/ks[i])**t; break
    print(f"{name}: k_x={'%.1f'%kx if kx else 'none'} | " + " ".join(parts))
print(f"\n=== LIMIT PROFILE n={NF} ({len(grown)} causets) ===")
print(f"(4.5*sqrt(112) = {4.5*math.sqrt(112):.0f}; quartile predictions: crossings ~ 4.5*sqrt(28,56,84,112) = 24,34,41,48)")
show(PA, "ALL      ")
for qi in range(4):
    show(PQ[qi], f"Q{qi+1} tops ")
print("DONE-LIMIT120")
