"""UV/IR MANIFOLD-LIKENESS SPLIT (registered 2026-08-17).
Motivation: gate-1's texture statistic uses ONLY N0,N1,N2 (0/1/2-
element intervals) - maximally UV.  The composite results showed
manifold-likeness EMERGING in the IR (profile -> 4D at k~256 while
UV deviated).  Question: do single grown 2D causets (standard BD
weights W2=(2,-4,2), phi=pi/4, converged ellipsoid law, sampled =
decohered ensemble) show the same split - UV texture high but IR
interval dimension -> 2?
READINGS: (i) d_int(k) descends toward 2 with growing k while UV
abundances stay off-sprinkling => manifold-likeness is an IR
phenomenon and the gate-1 criterion is UV-only; (ii) d_int(k) flat
or away from 2 at all k => grown causets are non-manifold-like at
every scale, gate-1 verdict is scale-robust; (iii) mixed/unclear.
Both grown ensemble AND matched 2D sprinklings measured with the
SAME estimator (sprinkling column = estimator calibration)."""
import numpy as np, math, time
T0=time.time()
def log(*a): print(f"[{time.time()-T0:6.1f}s]", *a, flush=True)
exec(open('selection_and_action.py').read().split('if MODE == "A":')[0])
from law_ellipsoid import make_law_ell
law = make_law_ell(math.pi/4, NSTART=16)
N = 64; M = 30
MM_D = np.array([1.5, 2, 3, 4, 5, 6, 8, 10], float)
MM_F = np.array([0.75, 0.5000, 0.2296, 0.0994, 0.0417, 0.0170, 0.00287, 0.000496])
_ORD = np.argsort(-np.log(MM_F)); _XP = (-np.log(MM_F))[_ORD]; _FP = MM_D[_ORD]
def d_from_f(f):
    if f is None or f <= 0: return float("nan")
    return float(np.interp(-math.log(f), _XP, _FP))
def grow(N):
    while True:
        below=[0]; above=[0]; ok=True
        for n in range(1, N):
            dlist=downsets_vec(n,np.array(below,dtype=np.int64)); garr=gaps_vec(dlist,n,np.array(above,dtype=np.int64))
            gc={}
            for g in garr.tolist(): gc[g]=gc.get(g,0)+1
            lw=law(gc)
            if lw is None: ok=False; break
            p=np.array([lw[g] for g in garr.tolist()]); p=np.maximum(p,0)
            if p.sum()<=0: ok=False; break
            p/=p.sum()
            j=rng.choice(dlist.shape[0],p=p)
            D=int(dlist[j]); below.append(D); above.append(0)
            m=D
            while m:
                d=(m&-m).bit_length()-1; above[d]|=1<<n; m&=m-1
        if ok: break
    R=np.zeros((N,N),dtype=bool)
    for x in range(N):
        m=below[x]
        while m:
            y=(m&-m).bit_length()-1; R[y,x]=True; m&=m-1
    return R
def sprink2d(N):
    u=rng.random(N); v=rng.random(N)
    R=np.zeros((N,N),dtype=bool)
    for i in range(N):
        R[i,:] = (u>u[i])&(v>v[i])
    return R
def measure(R, N):
    """UV abundances per element + interval profile d_int(k)."""
    # UV: N0,N1,N2 abundances (k-element intervals between related pairs covering)
    ab=np.zeros(3)
    npairs=0
    for x in range(N):
        for y in range(N):
            if R[y,x]:
                k=int((R[y,:]&R[:,x]).sum())
                if k<3: ab[k]+=1
                npairs+=1
    # IR: sub-order density in random large intervals
    prof={}
    got=0; tries=0
    while got<600 and tries<40000:
        tries+=1
        x,y=rng.integers(N),rng.integers(N)
        if not R[x,y]:
            x,y=y,x
            if not R[x,y]: continue
        inter=np.nonzero(R[x,:]&R[:,y])[0]
        k=len(inter)
        if k<4: continue
        sub=R[np.ix_(inter,inter)]
        b=2**int(math.log2(k))
        prof.setdefault(b,[]).append(sub.sum()/(k*(k-1)/2))
        got+=1
    r = R.sum()/(N*(N-1)/2)
    return ab/N, prof, r
def agg(runs):
    abm = np.mean([a for a,_,_ in runs],axis=0)
    rm = np.mean([r for _,_,r in runs])
    P={}
    for _,prof,_ in runs:
        for b,fs in prof.items(): P.setdefault(b,[]).extend(fs)
    return abm, P, rm
log("growing", M, "causets to n =", N)
gr=[measure(grow(N),N) for i in range(M)]
log("grown done; sprinkling")
sp=[measure(sprink2d(N),N) for i in range(M)]
abG,PG,rG = agg(gr); abS,PS,rS = agg(sp)
print(f"\nUV (abundances/N, n={N}):  grown={np.round(abG,3)}  sprinkling={np.round(abS,3)}")
print(f"UV texture |grown-sprink| = {np.linalg.norm(abG-abS):.4f}")
print(f"ordering fraction: grown r={rG:.4f}  sprinkling r={rS:.4f}  (2D expect 0.5)")
print(f"\nIR interval profile d_int(k)  [2D sprinkling column = estimator calibration]:")
print(f"  {'k':>5} {'grown':>7} {'sprink':>7}   (n per bin)")
for b in sorted(set(PG)&set(PS)):
    fg,fs = PG[b], PS[b]
    if len(fg)<15 or len(fs)<15: continue
    print(f"  {b:>5} {d_from_f(float(np.mean(fg))):>7.2f} {d_from_f(float(np.mean(fs))):>7.2f}   ({len(fg)}/{len(fs)})")
print("DONE-UVIR")
