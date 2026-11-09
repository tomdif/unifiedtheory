"""Convexity scale of the bare twisted Wilson action (numerics, not a proof).

Same quantity as yang_mills_preconditioned_hessian.py, but with the fluctuation supported on the links inside a block of
side l (Dirichlet restriction). lam(l, beta) = smallest generalized eigenvalue of Hess U + K b D D^T + 2I against
b Delta_0, both restricted to the block, minimized over blocks. It gives the largest scale l*(beta) where the bare
action is convex in the preconditioned sense: the base scale any multiscale Bakry-Emery / Polchinski scheme would start from.

Written before any run: 1 - lam(l) grows with l at fixed beta like the n-growth already seen (about l^0.65 at K = 1),
and l*(beta), where lam = 1/2, grows like a power of beta near 1/(2 * 0.65) ~ 0.77. If 1 - lam is flat in l instead,
the earlier n-growth was a twisted finite-volume effect, not a scale effect.
Usage: out N ls beta_stds n_blocks
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, scipy.sparse as sp, scipy.linalg as sl
from yang_mills_preconditioned_hessian import hessian, gauge_D, cool, gauge_fix, idx
from yang_mills_twisted_step_scaling import twist, heat, over

out=sys.argv[1]; N=int(sys.argv[2]); ls=[int(x) for x in sys.argv[3].split(',')]; bs=[float(x) for x in sys.argv[4].split(',')]; nb=int(sys.argv[5])
rng=np.random.default_rng(11); z=twist(N); par=np.indices((N,)*4).sum(0)%2
V=np.zeros((4,)+(N,)*4+(4,)); V[...,0]=1
for _ in range(100): heat(V,z,30.,rng,par); over(V,z,par)
cool(V,z,par); D0=gauge_D(V); Delta0=(hessian(V,z,1.)+D0@D0.T).tocsr(); I=idx(N)

def block_dofs(o,l):
    m=np.zeros((4,)+(N,)*4,bool)
    sl_=tuple(slice(None) for _ in range(0))
    c=np.indices((N,)*4); inside=np.ones((N,)*4,bool)
    for a in range(4): inside&=((c[a]-o[a])%N)<l
    for mu in range(4):
        head=np.roll(inside,-1,axis=mu)   # x+mu inside
        m[mu]=inside&head
    links=I[m]
    return np.sort((3*links[:,None]+np.arange(3)).ravel())

res=[]
for b in bs:
    U=V.copy()
    for _ in range(240): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
    best=None
    for c0 in (1,-1):
        for c3 in (1,-1):
            W=U.copy(); W[0][0]*=c0; W[3][:,:,:,0]*=c3; Wg,F=gauge_fix(W,V,par)
            if best is None or F>best[1]: best=(Wg,F)
    Wg=best[0]; D=gauge_D(Wg); Hn=hessian(Wg,z,b); H=(Hn+100*b*D@D.T).tocsr(); M=(b*Delta0).tocsr()
    origins=[rng.integers(0,N,4) for _ in range(nb)]
    for l in ls:
        lam=[]; lamn=[]
        for o in origins:
            k=block_dofs(o,l); Hb=H[k][:,k].toarray(); Mb=M[k][:,k].toarray()
            lamn.append(float(sl.eigh(Hb,Mb,eigvals_only=True,subset_by_index=[0,0])[0]))
            lam.append(float(sl.eigh(Hb+2*np.eye(len(k)),Mb,eigvals_only=True,subset_by_index=[0,0])[0]))
        r=dict(N=N,bstd=b,l=l,lam_min=min(lam),lam_mean=float(np.mean(lam)),lam_noric_min=min(lamn),lam_noric_mean=float(np.mean(lamn)))
        res.append(r); print(json.dumps(r),flush=True); json.dump(res,open(out,'w'))
