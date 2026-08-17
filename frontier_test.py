"""FRONTIER TEST (registered 2026-08-17, the window-scaling clincher).
Window-scaling found k_x ~ 4.5*sqrt(n): the d=2 crossing sits at
interval heights comparable to the causet height - the signature of
a growth-frontier artifact.  DIRECT TEST: on the same n=96 causets,
measure the interval profile twice: (a) all related pairs;
(b) BULK-RESTRICTED - top endpoint y must have >= 16 elements above
it (the interval cannot touch the frontier).
READINGS: (i) FRONTIER CONFIRMED: bulk-restricted profile's d=2
crossing recedes substantially or disappears (d >= 2 through the
measurable range) => the collapse is a frontier effect; the bulk is
manifold-compatible; global estimators (r, d_eff, deep-sampler
verdicts) must be re-scoped as frontier-contaminated.
(ii) NO CHANGE: bulk-restricted profile crosses at the same k_x =>
the collapse is bulk physics; window-scaling reading (i) dies.
(iii) partial shift => both effects present; quantify."""
import numpy as np, math, time
T0=time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)
from law_ellipsoid import make_law_ell
rng = np.random.default_rng(20260821)
law = make_law_ell(math.pi/4, NSTART=16, disk_cache="law_cache_pi4_16.pkl")
POP16 = np.array([bin(i).count("1") for i in range(1 << 16)], dtype=np.int64)
def popcount(arr):
    return (POP16[arr & 0xFFFF] + POP16[(arr >> 16) & 0xFFFF] +
            POP16[(arr >> 32) & 0xFFFF] + POP16[(arr >> 48) & 0x7FFF])
W2ARR = np.array([2, -4, 2, 0], dtype=np.int64)
LIMB = 60; LOWM = (1 << LIMB) - 1
IDEAL_CAP = 3_000_000; NF = 96; MARGIN = 16
def grow(N):
    for attempt in range(8):
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
            if lw is None: ok = False; break
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
            if len(ids0) > IDEAL_CAP: ok = False; break
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
def profiles(R, N):
    nabove = R.sum(axis=1)   # elements above y ... careful: R[y,x]=True means y<x
    # R[y,:].sum() = elements above y
    pAll = {}; pBulk = {}
    got = 0; tries = 0
    while got < 3000 and tries < 400000:
        tries += 1
        x, y = rng.integers(N), rng.integers(N)
        if not R[x, y]:
            x, y = y, x
            if not R[x, y]: continue
        # here R[x,y]: x below y; top endpoint = y
        inter = np.nonzero(R[x, :] & R[:, y])[0]
        k = len(inter)
        if k < 4: continue
        sub = R[np.ix_(inter, inter)]
        f = sub.sum()/(k*(k-1)/2)
        b = int(round(2*math.log2(k)))
        pAll.setdefault(b, []).append(f)
        if R[y, :].sum() >= MARGIN:
            pBulk.setdefault(b, []).append(f)
        got += 1
    return pAll, pBulk
M = 10
grown = []
for i in range(M):
    R = grow(NF)
    if R is not None: grown.append(R)
    law.persist()
log(f"{len(grown)} causets at n={NF}; profiling (margin={MARGIN})")
PA = {}; PB = {}
for R in grown:
    a, b = profiles(R, NF)
    for k, v in a.items(): PA.setdefault(k, []).extend(v)
    for k, v in b.items(): PB.setdefault(k, []).extend(v)
def show(P, name):
    ks = []; ds = []
    parts = []
    for b in sorted(P):
        fs = P[b]
        if len(fs) < 25: continue
        kmid = 2**(b/2)
        d = d_from_f(float(np.mean(fs)))
        ks.append(kmid); ds.append(d)
        parts.append(f"k{kmid:.0f}:{d:.2f}(n={len(fs)})")
    kx = None
    for i in range(len(ks)-1):
        if ds[i] >= 2.0 > ds[i+1]:
            t = (ds[i]-2.0)/(ds[i]-ds[i+1])
            kx = ks[i]*(ks[i+1]/ks[i])**t
            break
    print(f"{name}: k_x={'%.1f'%kx if kx else 'NONE (no crossing in range)'}")
    print("   " + " ".join(parts))
    return kx
print(f"\n=== FRONTIER TEST (n={NF}, {len(grown)} causets, margin={MARGIN}) ===")
kxA = show(PA, "ALL pairs      ")
kxB = show(PB, "BULK-restricted")
if kxA and kxB:
    print(f"crossing shift: {kxA:.1f} -> {kxB:.1f}  ({(kxB/kxA-1)*100:+.0f}%)")
elif kxA and not kxB:
    print("crossing DISAPPEARS under bulk restriction - reading (i) FRONTIER CONFIRMED")
print("DONE-FRONTIER")
