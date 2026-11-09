"""COMPOSITE SCALE-WINDOW STRESS TEST (registered 2026-08-17).
The dimensional-additivity mechanism says a product interval of
cardinality k samples each factor at scale ~sqrt(k):
    d_prod(k) ~ 2 * d_2D(sqrt k).
The flagship result (f(k~256) on the 4D benchmark to 1.4%) then
inherits from the factor MID-scale d_2D(16)~2.1.  But free-growth
factor profiles keep FALLING (d_2D(32)~1.7-1.9, deep-sampler
d_eff(80)=1.666).  Chained prediction: at k~1024 the composite
flows BELOW 4 to ~2*d_2D(32) ~ 3.6-3.8: "4D IR" would be a scale
WINDOW, not an asymptote.
TEST: n=64 factors (largest yet), 4096-element composites, profile
to k~1024, plus the factor profile measured on the SAME factors so
the transfer law is checked point-by-point.
READINGS: (i) WINDOW: d_int at k~512-1024 falls clearly below 3.9
AND tracks 2*d_2D(sqrt k) => rescope flagship as a scale window;
asymptote = 2*d_factor_IR unless factor drift is finite-size.
(ii) HOLD: stays ~4.0 at k~1024, transfer law must then FAIL at
large k => factor IR drift not inherited; investigate mechanism.
(iii) TRANSFER LAW FAILS at all k => additivity mechanism wrong."""
import numpy as np, math, time
T0=time.time()
def log(*a): print(f"[{time.time()-T0:6.1f}s]", *a, flush=True)
exec(open('selection_and_action.py').read().split('if MODE == "A":')[0])
from law_ellipsoid import make_law_ell
law = make_law_ell(math.pi/4, NSTART=16, disk_cache="law_cache_pi4_16.pkl")
NF = 64; NPAIR = 4
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
MM_D = np.array([1.5, 2, 3, 4, 5, 6, 8, 10], float)
MM_F = np.array([0.75, 0.5000, 0.2296, 0.0994, 0.0417, 0.0170, 0.00287, 0.000496])
_ORD = np.argsort(-np.log(MM_F)); _XP = (-np.log(MM_F))[_ORD]; _FP = MM_D[_ORD]
def d_from_f(f):
    if f is None or f <= 0: return float("nan")
    return float(np.interp(-math.log(f), _XP, _FP))
def profile(R, N, want=1200, cap=90000):
    prof={}
    got=0; tries=0
    while got<want and tries<cap:
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
    return prof
def agg(profs):
    P={}
    for prof in profs:
        for b,fs in prof.items(): P.setdefault(b,[]).extend(fs)
    return P
log(f"growing {2*NPAIR} factors to n={NF}")
factors=[grow(NF) for _ in range(2*NPAIR)]
law.persist()
log("factors done; measuring factor profiles")
PF = agg([profile(F, NF, want=800) for F in factors])
rF = np.mean([F.sum()/(NF*(NF-1)/2) for F in factors])
log("building composites")
comps=[np.kron(factors[2*i], factors[2*i+1]) for i in range(NPAIR)]
NC = NF*NF
rC = np.mean([Cm.sum()/(NC*(NC-1)/2) for Cm in comps])
PC = agg([profile(Cm, NC, want=1500, cap=150000) for Cm in comps])
print(f"\nFACTORS (n={NF}): r={rF:.4f}  (2D sprinkling 0.50)")
print("factor profile d_2D(k):")
fac_k=[]; fac_d=[]
for b in sorted(PF):
    fs=PF[b]
    if len(fs)<20: continue
    d=d_from_f(float(np.mean(fs)))
    fac_k.append(b); fac_d.append(d)
    print(f"   k~{b:5d}: d_2D={d:.2f}  (f={np.mean(fs):.4f}, n={len(fs)})")
print(f"\nCOMPOSITES ({NC} elements): r={rC:.4f}  (4D benchmark 0.0994, iid dominance 0.125)")
print("product profile vs transfer-law prediction 2*d_2D(sqrt k):")
lk = np.log2(np.array(fac_k,float)); ld = np.array(fac_d)
for b in sorted(PC):
    fs=PC[b]
    if len(fs)<20: continue
    d=d_from_f(float(np.mean(fs)))
    pred = 2*float(np.interp(math.log2(math.sqrt(b)), lk, ld))
    print(f"   k~{b:5d}: d_prod={d:.2f}  pred={pred:.2f}  (f={np.mean(fs):.5f}, n={len(fs)})")
print("\n4D benchmark f-values: k-independent 0.0994 (d=4).")
print("DONE-STRESS")
