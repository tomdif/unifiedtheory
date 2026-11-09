"""Exact r(L) of the flowed block action density for the free lattice gauge field (numerics, not a proof).

Same definition as yang_mills_scale_corr_gauge.py at leading order: O = sum_{m<n} F_mn^2 / 2, flow factor (1 - eps phat^2)^steps
on each field, block side L, separation 2L. Wick: Cov(O(x), O(y)) = (1/2) sum_{m<n, r<s} G_{mn,rs}(x-y)^2. The zero mode is removed.
This is the massless reference for the Coulomb phase and for SU(2) at weak coupling. It does not depend on the gauge coupling.
"""
import os
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
import numpy as np, json, sys
EPS=.05
def run(N,L):
    steps=int(round(L*L/8/EPS)); k=2*np.pi*np.fft.fftfreq(N)
    K=np.meshgrid(k,k,k,k,indexing='ij',sparse=True)
    q=[np.exp(1j*x)-1 for x in K]; ph=sum(4*np.sin(x/2)**2 for x in K)
    inv=np.zeros(ph.shape); inv[ph>1e-12]=1/ph[ph>1e-12]
    f2=(1-EPS*ph)**(2*steps)
    C=np.zeros((N,)*4)
    pl=[(m,n) for m in range(4) for n in range(m+1,4)]
    d=lambda a,b:1. if a==b else 0.
    for (m,n) in pl:
        for (r,s) in pl:
            g=0
            if d(n,s): g=g+q[m]*np.conj(q[r])
            if d(n,r): g=g-q[m]*np.conj(q[s])
            if d(m,s): g=g-q[n]*np.conj(q[r])
            if d(m,r): g=g+q[n]*np.conj(q[s])
            if np.isscalar(g): continue
            C+=np.fft.ifftn(g*inv*f2).real**2
    # Block filter on the separation z: the triangular weight is the autocorrelation of a block.
    w1=np.zeros(N); w1[:L]=1/L; W=np.fft.fft(w1); W2=np.abs(W)**2
    F=np.fft.fftn(C)
    for ax in range(4):
        sh=[1]*4; sh[ax]=N; F=F*W2.reshape(sh)
    B=np.fft.ifftn(F).real
    s=2*L; cs=np.mean([np.take(B,s,axis=ax)[(0,)*3] for ax in range(4)])
    return float(cs/B[0,0,0,0])
out={}
for N in (16,32,48):
    out[N]={L:run(N,L) for L in (1,2,4,8) if 4*L<=N}
    print(N,{L:round(v,5) for L,v in out[N].items()},flush=True)
json.dump(out,open('data/yang_mills_scale_corr_freegauge_2026_10_31.json','w'),indent=1)
