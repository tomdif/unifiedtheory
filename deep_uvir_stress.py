"""UV/IR SPLIT + COMPOSITE SCALE-WINDOW STRESS (v2, ideal-lattice
growth; v1 died: downsets_vec brute-forces 2^n masks, OOM-killed at
n~30).  Grows n=64 causets under the STANDARD 2D law (W2=(2,-4,2),
phi=pi/4, converged ellipsoid maxent member, disk-cached) via the
deep sampler's incremental ideal-lattice update (cost ~ #ideals).

EXPERIMENT A (UV/IR split, registered 2026-08-17): 30 causets;
UV = (N0,N1,N2)/n abundances vs matched sprinkling; IR = d_int(k)
interval profile vs sprinkling calibration column.  Readings:
(i) IR -> 2 while UV off => gate-1 criterion is UV-only;
(ii) off-manifold at all scales => scale-robust negative;
(iii) mixed.

EXPERIMENT B (composite window stress, registered 2026-08-17):
8 of the same causets -> 4 composites (4096 elements), profile to
k~1024, vs transfer law d_prod(k) = 2*d_2D(sqrt k) measured on the
same factors.  Readings: (i) WINDOW (d_prod(k~512+) < 3.9 tracking
transfer law) => flagship 4D result is a scale window;
(ii) HOLD ~4.0 => factor IR drift not inherited;
(iii) transfer law fails everywhere => mechanism wrong."""
import numpy as np, math, time
T0=time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)
from law_ellipsoid import make_law_ell
rng = np.random.default_rng(20260817)
law = make_law_ell(math.pi/4, NSTART=16, disk_cache="law_cache_pi4_16.pkl")
POP16 = np.array([bin(i).count("1") for i in range(1 << 16)], dtype=np.int64)
def popcount(arr):
    return (POP16[arr & 0xFFFF] + POP16[(arr >> 16) & 0xFFFF] +
            POP16[(arr >> 32) & 0xFFFF] + POP16[(arr >> 48) & 0x7FFF])
W2ARR = np.array([2, -4, 2, 0], dtype=np.int64)
LIMB = 60; LOWM = (1 << LIMB) - 1
NF = 64; IDEAL_CAP = 3_000_000
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
            m = D
            while m:
                d = (m & -m).bit_length()-1; above[d] |= 1 << n; m &= m-1
        if ok: break
    else:
        return None
    R = np.zeros((N, N), dtype=bool)
    for x in range(N):
        m = below[x]
        while m:
            y = (m & -m).bit_length()-1; R[y, x] = True; m &= m-1
    return R
def sprink2d(N):
    u = rng.random(N); v = rng.random(N)
    R = np.zeros((N, N), dtype=bool)
    for i in range(N):
        R[i, :] = (u > u[i]) & (v > v[i])
    return R
MM_D = np.array([1.5, 2, 3, 4, 5, 6, 8, 10], float)
MM_F = np.array([0.75, 0.5000, 0.2296, 0.0994, 0.0417, 0.0170, 0.00287, 0.000496])
_ORD = np.argsort(-np.log(MM_F)); _XP = (-np.log(MM_F))[_ORD]; _FP = MM_D[_ORD]
def d_from_f(f):
    if f is None or f <= 0: return float("nan")
    return float(np.interp(-math.log(f), _XP, _FP))
def uv_abund(R, N):
    ab = np.zeros(3)
    for x in range(N):
        for y in range(N):
            if R[y, x]:
                k = int((R[y, :] & R[:, x]).sum())
                if k < 3: ab[k] += 1
    return ab / N
def profile(R, N, want=1000, cap=100000):
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
        b = 2**int(math.log2(k))
        prof.setdefault(b, []).append(sub.sum()/(k*(k-1)/2))
        got += 1
    return prof
def agg(profs):
    P = {}
    for prof in profs:
        for b, fs in prof.items(): P.setdefault(b, []).extend(fs)
    return P
M = 30
log(f"growing {M} causets to n={NF} (ideal-lattice)")
grown = []
for i in range(M):
    R = grow(NF)
    if R is None: log(f"  causet {i}: FAILED 8 attempts"); continue
    grown.append(R)
    if (i+1) % 5 == 0: log(f"  {i+1}/{M} grown"); law.persist()
law.persist()
log(f"{len(grown)} causets grown; measuring; sprinkling column")
spr = [sprink2d(NF) for _ in range(M)]
abG = np.mean([uv_abund(R, NF) for R in grown], axis=0)
abS = np.mean([uv_abund(R, NF) for R in spr], axis=0)
rG = np.mean([R.sum()/(NF*(NF-1)/2) for R in grown])
rS = np.mean([R.sum()/(NF*(NF-1)/2) for R in spr])
PG = agg([profile(R, NF, want=600) for R in grown])
PS = agg([profile(R, NF, want=600) for R in spr])
print(f"\n=== EXPERIMENT A: UV/IR SPLIT (free growth, n={NF}) ===")
print(f"UV abundances/N: grown={np.round(abG,3)}  sprinkling={np.round(abS,3)}  |diff|={np.linalg.norm(abG-abS):.4f}")
print(f"ordering fraction: grown r={rG:.4f}  sprinkling r={rS:.4f}  (2D manifold 0.5)")
print(f"IR profile d_int(k)   [sprinkling column = estimator calibration]:")
fac_k=[]; fac_d=[]
for b in sorted(set(PG) | set(PS)):
    fg = PG.get(b, []); fs = PS.get(b, [])
    if len(fg) < 20: continue
    d = d_from_f(float(np.mean(fg)))
    ds = d_from_f(float(np.mean(fs))) if len(fs) >= 20 else float("nan")
    fac_k.append(b); fac_d.append(d)
    print(f"   k~{b:5d}: grown={d:5.2f}  sprink={ds:5.2f}   (n={len(fg)}/{len(fs)})")
print(f"\n=== EXPERIMENT B: COMPOSITE WINDOW STRESS (4 composites, {NF*NF} elements) ===")
comps = [np.kron(grown[2*i], grown[2*i+1]) for i in range(4)]
NC = NF*NF
rC = np.mean([Cm.sum()/(NC*(NC-1)/2) for Cm in comps])
PC = agg([profile(Cm, NC, want=1500, cap=200000) for Cm in comps])
print(f"composite r={rC:.4f}  (4D benchmark 0.0994, iid dominance-4 0.125)")
print("product profile vs transfer law 2*d_2D(sqrt k):")
lk = np.log2(np.array(fac_k, float)); ld = np.array(fac_d)
for b in sorted(PC):
    fs = PC[b]
    if len(fs) < 20: continue
    d = d_from_f(float(np.mean(fs)))
    pred = 2*float(np.interp(math.log2(math.sqrt(b)), lk, ld))
    print(f"   k~{b:5d}: d_prod={d:5.2f}  transfer-pred={pred:5.2f}  (f={np.mean(fs):.5f}, n={len(fs)})")
print("DONE-DEEP-UVIR")
