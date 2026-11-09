"""Twisted 4D lattice Sobolev constant (numerics, not a proof).

C_S(n) = max ||a||_4 / <a, Delta_0 a>^(1/2) over horizontal adjoint 1-forms a at the twisted flat vacuum, where
||a||_4^4 = sum_e |a_e|^4 (lattice units). Scale-invariant coercivity (README, "Cheapest large-field direction")
needs C_S bounded in n. The Hausdorff-Young proof gives only C_S <= C (log n)^(1/4); a Gagliardo-Nirenberg proof gives
no log. Maximized by projected gradient ascent on the sphere E = 1 from several starts (local and spread).
Written before any run: C_S(n) is flat in n within a few percent, and the maximizer is localized at lattice scale.
Usage: out ns n_starts
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, scipy.sparse.linalg as sla
from yang_mills_preconditioned_hessian import hessian, gauge_D, cool
from yang_mills_twisted_step_scaling import twist, heat, over

out=sys.argv[1]; ns=[int(x) for x in sys.argv[2].split(',')]; ns_=int(sys.argv[3]); res=[]
for N in ns:
    rng=np.random.default_rng(31+N); z=twist(N); par=np.indices((N,)*4).sum(0)%2
    V=np.zeros((4,)+(N,)*4+(4,)); V[...,0]=1
    for _ in range(100): heat(V,z,30.,rng,par); over(V,z,par)
    cool(V,z,par); D0=gauge_D(V); Delta0=(hessian(V,z,1.)+D0@D0.T).tocsr(); d=Delta0.shape[0]
    L=sla.splu((D0.T@D0).tocsc()); proj=lambda x:x-D0@L.solve(D0.T@x)
    Linv=sla.splu(Delta0.tocsc())
    def q4(a): return float(((a.reshape(-1,3)**2).sum(1)**2).sum())
    best=0; bestpr=None
    for s in range(ns_):
        r=np.random.default_rng(s)
        a=r.normal(size=d)
        if s%2==0:   # localized start
            a=np.zeros(d); k=r.integers(0,d//3); a[3*k:3*k+3]=r.normal(size=3)
        a=proj(a); a/=np.sqrt(a@(Delta0@a))
        for it in range(3000):
            g=4*((a.reshape(-1,3)**2).sum(1)[:,None]*a.reshape(-1,3)).ravel()
            # Riemannian ascent on {E = 1}: precondition by Delta0^-1, project, retract
            step=proj(Linv.solve(g)); step-= a*(a@(Delta0@step))
            a=a+0.5*step/np.sqrt(max(q4(a),1e-300)); a=proj(a); a/=np.sqrt(a@(Delta0@a))
        val=q4(a)**0.25
        site=(a.reshape(4,N**4,3)**2).sum((0,2)); site/=site.sum(); pr=float(1/(site**2).sum())
        if val>best: best=val; bestpr=pr
    r_=dict(N=N,C_S=best,participation_sites=bestpr); res.append(r_); print(json.dumps(r_),flush=True); json.dump(res,open(out,'w'))
