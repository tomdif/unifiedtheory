"""SQRT-WIDTH PINNING (registered 2026-08-17, window-law corollary).
The window law says free 2D growth crosses d=2 at a finite scale
because its geometry drifts (width grows linearly, r -> 0.66).  2D
diamond sprinklings have width ~ 2*sqrt(n) - a SQRT width profile.
TEST: constrain growth to w(n) = a*sqrt(n) (band +-1, free below
n=6) for a in {1.0, 1.5, 2.0, 3.0}; 8 causets each to n=64;
measure d_int(k) profile + r.  If some a pins the profile FLAT at
~2.0 (sprinkling-like at every scale), build 4 composites (4096
elements) from those factors and test whether d_prod holds ~4.0
flat - turning the 4D window into an asymptote.
READINGS: (i) PIN: some a gives |d_int(k)-2| <= ~0.15 across
k=4..32 AND its composite holds d_prod in [3.8, 4.3] through
k~1024 => constructive 4D asymptote found; (ii) PARTIAL: profile
flattens but off 2 (e.g. 2.2-2.3 as linear rules gave) => products
plateau off 4; (iii) NO PIN: sqrt rule still drifts => width is
not the binding variable."""
import numpy as np, math, time
T0=time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)
from law_ellipsoid import make_law_ell
rng = np.random.default_rng(20260818)
law = make_law_ell(math.pi/4, NSTART=16, disk_cache="law_cache_pi4_16.pkl")
POP16 = np.array([bin(i).count("1") for i in range(1 << 16)], dtype=np.int64)
def popcount(arr):
    return (POP16[arr & 0xFFFF] + POP16[(arr >> 16) & 0xFFFF] +
            POP16[(arr >> 32) & 0xFFFF] + POP16[(arr >> 48) & 0x7FFF])
W2ARR = np.array([2, -4, 2, 0], dtype=np.int64)
LIMB = 60; LOWM = (1 << LIMB) - 1
NF = 64; IDEAL_CAP = 3_000_000; RAMP = 6; BAND = 1
def grow(N, a):
    for attempt in range(10):
        below = [0]; above = [0]
        ids0 = np.array([0, 1], dtype=np.int64)
        ids1 = np.array([0, 0], dtype=np.int64)
        ok = True; fallback = 0
        for n in range(1, N):
            m = len(ids0)
            gaps = np.ones(m, dtype=np.int64)
            maxcnt = np.zeros(m, dtype=np.int64)
            for y in range(n):
                iy = ((ids0 >> y) & 1) == 1 if y < LIMB else ((ids1 >> (y - LIMB)) & 1) == 1
                if not iy.any(): continue
                A0 = np.int64(above[y] & LOWM); A1 = np.int64(above[y] >> LIMB)
                k = popcount(ids0 & A0) + popcount(ids1 & A1)
                gaps -= np.where(iy, W2ARR[np.minimum(k, 3)], 0)
                maxcnt += (iy & (k == 0)).astype(np.int64)
            if n < RAMP:
                sel = np.ones(m, dtype=bool)
            else:
                wn = max(2, round(a*math.sqrt(n)))
                sel = (maxcnt >= wn - BAND) & (maxcnt <= wn + BAND)
                if not sel.any():
                    avail = maxcnt[maxcnt > 0]
                    if avail.size == 0: ok = False; break
                    cands = np.unique(avail)
                    lower = cands[cands < wn]
                    wbest = int(lower.max()) if lower.size else int(cands.min())
                    sel = maxcnt == wbest
                    fallback += 1
            gsel = gaps[sel]
            gu, inv = np.unique(gsel, return_inverse=True)
            gc = dict(zip(gu.tolist(), np.bincount(inv).tolist()))
            lw = law(gc)
            if lw is None: ok = False; break
            lw_arr = np.array([lw[g] for g in gu.tolist()])
            probs = np.maximum(lw_arr[inv], 0)
            s = probs.sum()
            if s <= 0: ok = False; break
            idxs = np.nonzero(sel)[0]
            j = idxs[rng.choice(len(idxs), p=probs/s)]
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
        return None, None
    R = np.zeros((N, N), dtype=bool)
    for x in range(N):
        mm = below[x]
        while mm:
            y = (mm & -mm).bit_length()-1; R[y, x] = True; mm &= mm-1
    return R, fallback
MM_D = np.array([1.5, 2, 3, 4, 5, 6, 8, 10], float)
MM_F = np.array([0.75, 0.5000, 0.2296, 0.0994, 0.0417, 0.0170, 0.00287, 0.000496])
_ORD = np.argsort(-np.log(MM_F)); _XP = (-np.log(MM_F))[_ORD]; _FP = MM_D[_ORD]
def d_from_f(f):
    if f is None or f <= 0: return float("nan")
    return float(np.interp(-math.log(f), _XP, _FP))
def profile(R, N, want=800, cap=100000):
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
        prof.setdefault(2**int(math.log2(k)), []).append(sub.sum()/(k*(k-1)/2))
        got += 1
    return prof
def agg(profs):
    P = {}
    for prof in profs:
        for b, fs in prof.items(): P.setdefault(b, []).extend(fs)
    return P
best = None
RES = {}
for a in (1.0, 1.5, 2.0, 3.0):
    grown = []; fbs = []
    for i in range(8):
        R, fb = grow(NF, a)
        if R is None: log(f"a={a}: causet {i} FAILED"); continue
        grown.append(R); fbs.append(fb)
    law.persist()
    if len(grown) < 4:
        log(f"a={a}: too few causets ({len(grown)})"); continue
    rG = np.mean([R.sum()/(NF*(NF-1)/2) for R in grown])
    P = agg([profile(R, NF) for R in grown])
    row = []
    for b in sorted(P):
        fs = P[b]
        if len(fs) < 20: continue
        row.append((b, d_from_f(float(np.mean(fs))), len(fs)))
    rms = math.sqrt(np.mean([(d-2.0)**2 for b, d, _ in row if 4 <= b <= 32])) if row else 9
    RES[a] = (grown, rG, row, rms, np.mean(fbs))
    log(f"a={a}: r={rG:.4f} fallbacks/path={np.mean(fbs):.1f} profile=" +
        " ".join(f"k{b}:{d:.2f}" for b, d, _ in row) + f"  RMS_from_2={rms:.3f}")
    if best is None or rms < RES[best][3]: best = a
print(f"\nBEST PIN: a={best} (RMS from 2 = {RES[best][3]:.3f})")
grown, rG, row, rms, _ = RES[best]
print(f"factor r={rG:.4f}; profile: " + " ".join(f"k~{b}:{d:.2f}(n={n})" for b, d, n in row))
if rms <= 0.25 and len(grown) >= 8:
    print("\npin good enough - building 4 composites from best-a factors")
    comps = [np.kron(grown[2*i], grown[2*i+1]) for i in range(4)]
    NC = NF*NF
    rC = np.mean([Cm.sum()/(NC*(NC-1)/2) for Cm in comps])
    PC = agg([profile(Cm, NC, want=1500, cap=200000) for Cm in comps])
    print(f"composite r={rC:.4f} (4D benchmark 0.0994)")
    for b in sorted(PC):
        fs = PC[b]
        if len(fs) < 20: continue
        print(f"   k~{b:5d}: d_prod={d_from_f(float(np.mean(fs))):5.2f}  (f={np.mean(fs):.5f}, n={len(fs)})")
else:
    print("pin not achieved (reading ii/iii) - composite step skipped")
print("DONE-SQRTPIN")
