"""WINDOW SCALING (registered 2026-08-17). The free-growth manifold
window edge sits at k_x ~ n/2 at both measured sizes (k~16 at n=32,
k~32 at n=64; composite crossings match the squares exactly).
HYPOTHESIS: the window scales WITH the universe - the flow-through
beyond k_x is a finite-size frontier effect, and the bulk is
asymptotically 2D.  TEST: free growth (standard 2D law, converged
solver) at n = 32, 48, 64, 96; per n: interval profile, crossing
scale k_x(n) (interpolated d=2 crossing), and d_int at FIXED
k = 8, 16 across n.
READINGS: (i) SCALING WINDOW: k_x(n) ~ c*n (c ~ 0.5) AND fixed-k
d_int rises/converges above 2 => bulk is asymptotically manifold-
like; global negatives are frontier artifacts; gate-1-style
verdicts must be re-scoped to bulk observables.
(ii) SATURATING WINDOW: k_x(n) saturates => window is a fixed
scale; flow-through is bulk physics; deep-sampler verdict stands.
(iii) mixed/unclear."""
import numpy as np, math, time
T0=time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)
from law_ellipsoid import make_law_ell
rng = np.random.default_rng(20260820)
law = make_law_ell(math.pi/4, NSTART=16, disk_cache="law_cache_pi4_16.pkl")
POP16 = np.array([bin(i).count("1") for i in range(1 << 16)], dtype=np.int64)
def popcount(arr):
    return (POP16[arr & 0xFFFF] + POP16[(arr >> 16) & 0xFFFF] +
            POP16[(arr >> 32) & 0xFFFF] + POP16[(arr >> 48) & 0x7FFF])
W2ARR = np.array([2, -4, 2, 0], dtype=np.int64)
LIMB = 60; LOWM = (1 << LIMB) - 1
IDEAL_CAP = 3_000_000
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
def profile_fine(R, N, want=1200, cap=150000):
    """bins at powers of sqrt(2) for finer k_x interpolation"""
    prof = {}
    got = 0; tries = 0
    while got < want and tries < cap:
        tries += 1
        x, y = rng.integers(N), rng.integers(N)
        if not R[x, y]:
            x, y = y, x
            if not R[x, y]: continue
        inter = np.nonzero(R[x, :] & R[:, y])[0]
        k = len(inter)
        if k < 4: continue
        sub = R[np.ix_(inter, inter)]
        b = int(round(2*math.log2(k)))   # sqrt2-power bin index
        prof.setdefault(b, []).append(sub.sum()/(k*(k-1)/2))
        got += 1
    return prof
PLAN = [(96, 8)]
SUMMARY = []
for N, M in PLAN:
    grown = []
    for i in range(M):
        R = grow(N)
        if R is not None: grown.append(R)
    law.persist()
    P = {}
    for R in grown:
        for b, fs in profile_fine(R, N).items(): P.setdefault(b, []).extend(fs)
    rG = np.mean([R.sum()/(N*(N-1)/2) for R in grown])
    ks=[]; ds=[]
    parts=[]
    for b in sorted(P):
        fs = P[b]
        if len(fs) < 25: continue
        kmid = 2**(b/2)
        d = d_from_f(float(np.mean(fs)))
        ks.append(kmid); ds.append(d)
        parts.append(f"k{kmid:.0f}:{d:.2f}")
    # interpolated crossing of d=2 (first downward crossing)
    kx = None
    for i in range(len(ks)-1):
        if ds[i] >= 2.0 > ds[i+1]:
            t = (ds[i]-2.0)/(ds[i]-ds[i+1])
            kx = ks[i]*(ks[i+1]/ks[i])**t
            break
    d8 = float(np.interp(math.log2(8), np.log2(ks), ds)) if len(ks)>1 else float("nan")
    d16 = float(np.interp(math.log2(16), np.log2(ks), ds)) if len(ks)>1 else float("nan")
    SUMMARY.append((N, len(grown), rG, kx, d8, d16))
    log(f"n={N} ({len(grown)} causets): r={rG:.4f} k_x={'%.1f'%kx if kx else 'none'} d(8)={d8:.2f} d(16)={d16:.2f} | " + " ".join(parts))
print("\n=== WINDOW SCALING SUMMARY ===")
print(f"{'n':>4} {'r':>7} {'k_x':>6} {'k_x/n':>6} {'d(8)':>5} {'d(16)':>6}")
for N, M, rG, kx, d8, d16 in SUMMARY:
    print(f"{N:>4} {rG:>7.4f} {('%.1f'%kx if kx else '  -'):>6} {('%.3f'%(kx/N) if kx else '  -'):>6} {d8:>5.2f} {d16:>6.2f}")
print("reading (i) if k_x/n ~ const and d(8),d(16) rise/converge; (ii) if k_x saturates")
print("DONE-WINDOWSCALE")
