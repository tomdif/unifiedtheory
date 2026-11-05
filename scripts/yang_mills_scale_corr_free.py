"""Scale correlation r(L) of a free lattice scalar in 4D, exact in infinite volume (numerics, not a proof).

r(L, s) = Corr(block average over side L at 0, block average displaced by s along one axis).
Uses 1/(p^2+m^2) = int dt exp(-t m^2) prod_i exp(-t phat_i^2), so every integral factorizes into 1D ones.
Prediction to be tested, stated before the run:
  massless: r(L, s=cL) tends to a constant r* as L grows.
  massive, separated blocks s=2L: r(2L) is about r(L)^2 when mL is large.
  massive, touching blocks s=L: decays like 1/(mL), so r(2L) is about r(L)/2 and the square law fails.
Conditioning on the parent block is not tested: for white noise it gives -1/(2^d - 1), not 0.
"""
import os
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
import numpy as np, json, sys
P=np.linspace(-np.pi,np.pi,20001)[:-1]; P=P+(P[1]-P[0])/2; dp=P[1]-P[0]
ph2=4*np.sin(P/2)**2
TS=np.exp(np.linspace(np.log(1e-3),np.log(1e7),700)); dlog=np.log(TS[1]/TS[0])
def D2(L):
    n=np.sin(L*P/2)**2; d=(L**2)*np.sin(P/2)**2
    return n/d
def I(L,s):
    w=D2(L)*np.cos(P*s)
    return np.array([(np.exp(-t*ph2)*w).sum()*dp/(2*np.pi) for t in TS])
def r(L,s,m):
    i0=I(L,0); i=I(L,s); wt=TS*np.exp(-TS*m*m)*dlog
    return float((wt*i*i0**3).sum()/(wt*i0**4).sum())
out=[]
Ls=[1,2,4,8,16,32,64]
for m in (0.,.01,.03,.1,.3):
    row=dict(m=m,L=Ls,touch=[r(L,L,m) for L in Ls],sep=[r(L,2*L,m) for L in Ls])
    out.append(row); print('m',m); print(' touch',[round(x,5) for x in row['touch']]); print(' sep  ',[round(x,6) for x in row['sep']],flush=True)
    s=row['sep']; t=row['touch']
    print(' sep r(2L)/r(L)^2 ',[round(s[i+1]/s[i]**2,3) if s[i]>0 else None for i in range(len(s)-1)])
    print(' touch r(2L)/r(L) ',[round(t[i+1]/t[i],3) for i in range(len(t)-1)])
json.dump(out,open('data/yang_mills_scale_corr_free_2026_10_31.json','w'),indent=1)
