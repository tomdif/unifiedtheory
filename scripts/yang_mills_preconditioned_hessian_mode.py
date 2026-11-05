"""Where the minimizing direction of the preconditioned Hessian lives (numerics, not a proof).

For each config: v = argmin <v,Hv>/<v, b Delta_0 v>. Reports q = <v,Delta_0 v>/<v,v> (wavelength: Delta_0 spans
[4 sin^2(pi/2n), ~16]) and the participation ratio of the per-site weight |v|^2 divided by n^4 (1 = spread, ~0 = local).
Also the spectrum of H - b Delta_0 split into its own extreme eigenvalues, to see whether the deficit is a local
negative eigenvalue of size ~ b g or a low-mode softening.
Usage: out ns beta_stds
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, scipy.sparse as sp
from scipy.sparse.linalg import lobpcg, LinearOperator, cg
from yang_mills_preconditioned_hessian import hessian, gauge_D, cool, gauge_fix
from yang_mills_twisted_step_scaling import twist, heat, over

out=sys.argv[1]; ns=[int(x) for x in sys.argv[2].split(',')]; bs=[float(x) for x in sys.argv[3].split(',')]; res=[]
for N in ns:
    rng=np.random.default_rng(7+N); z=twist(N); par=np.indices((N,)*4).sum(0)%2
    V=np.zeros((4,)+(N,)*4+(4,)); V[...,0]=1
    for _ in range(100): heat(V,z,30.,rng,par); over(V,z,par)
    cool(V,z,par); D0=gauge_D(V); Delta0=(hessian(V,z,1.)+D0@D0.T).tocsr(); d=Delta0.shape[0]
    for b in bs:
        U=V.copy()
        for _ in range(240): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
        best=None
        for c0 in (1,-1):
            for c3 in (1,-1):
                W=U.copy(); W[0][0]*=c0; W[3][:,:,:,0]*=c3; Wg,F=gauge_fix(W,V,par)
                if best is None or F>best[1]: best=(Wg,F)
        Wg=best[0]; D=gauge_D(Wg); H=(hessian(Wg,z,b)+b*D@D.T).tocsr(); M=(b*Delta0).tocsr()
        f=lambda x:np.stack([cg(M,c,rtol=1e-6,maxiter=500)[0] for c in np.asarray(x).reshape(d,-1).T],1).reshape(np.asarray(x).shape)
        Minv=LinearOperator((d,d),matvec=f,matmat=f)
        w,X=lobpcg(H,np.random.default_rng(0).normal(size=(d,4)),B=M,M=Minv,largest=False,tol=1e-7,maxiter=600)
        v=X[:,np.argmin(w)]; q=float(v@(Delta0@v)/(v@v))
        site=(v.reshape(4,N**4,3)**2).sum((0,2)); site/=site.sum(); pr=float(1/(site**2).sum()/N**4)
        E=(H-M).tocsr(); emin=float(lobpcg(E,np.random.default_rng(2).normal(size=(d,4)),largest=False,tol=1e-6,maxiter=600)[0].min())
        r=dict(N=N,bstd=b,lam=float(w.min()),q=q,q_range=[float(4*np.sin(np.pi/(2*N))**2),16.],pr=pr,min_eig_H_minus_bDelta0=emin)
        res.append(r); print(json.dumps(r),flush=True); json.dump(res,open(out,'w'))
