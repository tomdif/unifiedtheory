"""Averaged (effective) long-wavelength stiffness of the twisted lattice gauge field (numerics, not a proof).

The pointwise Hessian of the bare action is not convex beyond l* ~ 1/g (yang_mills_convexity_scale.py). Any multiscale
convexity scheme instead needs the coarse marginal to be convex, with Hess U_eff >= c beta Delta_0 on long modes. A
Brascamp-Lieb bound for that marginal gives Var<v,a> <= 1/(c beta q_v) for a Delta_0 eigenmode v with eigenvalue q_v.
Measured: r = beta_std q_v Var<v,a> over the lowest modes, with a = log(U V^-1) in background Landau gauge (best center
sector). Free field: r = 1.

Written before any run: r stays O(1) and grows at most like 1 + c g^2 log n at fixed beta, matching the logarithmic
running of the coupling. A power-law growth in n would kill the averaged route as well as the pointwise one.
Usage: out ns beta_stds n_cfg n_modes
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np
from scipy.sparse.linalg import lobpcg
from yang_mills_preconditioned_hessian import hessian, gauge_D, cool, gauge_fix
from yang_mills_twisted_step_scaling import twist, heat, over, qmul, qc

def qlog(q):
    w=np.clip(q[...,0],-1,1); s=np.linalg.norm(q[...,1:],axis=-1,keepdims=True); th=np.arctan2(s,w[...,None])
    return np.where(s>1e-14,th/np.maximum(s,1e-300),1.)*q[...,1:]

out=sys.argv[1]; ns=[int(x) for x in sys.argv[2].split(',')]; bs=[float(x) for x in sys.argv[3].split(',')]
ncfg=int(sys.argv[4]); nm=int(sys.argv[5]); res=[]
for N in ns:
    rng=np.random.default_rng(5+N); z=twist(N); par=np.indices((N,)*4).sum(0)%2
    V=np.zeros((4,)+(N,)*4+(4,)); V[...,0]=1
    for _ in range(100): heat(V,z,30.,rng,par); over(V,z,par)
    cool(V,z,par); D0=gauge_D(V); Delta0=(hessian(V,z,1.)+D0@D0.T).tocsr(); d=Delta0.shape[0]
    # lowest modes, restricted to horizontal at V (D0^T v = 0): penalize vertical part heavily
    P=(hessian(V,z,1.)+100*D0@D0.T).tocsr()
    q,E=lobpcg(P,np.random.default_rng(3).normal(size=(d,nm)),largest=False,tol=1e-9,maxiter=2000)
    o=np.argsort(q); q=q[o]; E=E[:,o]
    print('N',N,'modes q',np.round(q,4).tolist(),flush=True)
    for b in bs:
        U=V.copy()
        for _ in range(300): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
        amps=[]
        for c in range(ncfg):
            for _ in range(20): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
            best=None
            for c0 in (1,-1):
                for c3 in (1,-1):
                    W=U.copy(); W[0][0]*=c0; W[3][:,:,:,0]*=c3; Wg,F=gauge_fix(W,V,par)
                    if best is None or F>best[1]: best=(Wg,F)
            a=np.stack([qlog(qmul(best[0][m],qc(V[m]))) for m in range(4)]).ravel()
            amps.append(E.T@a)
        A=np.array(amps); var=A.var(0,ddof=1)
        # modes are degenerate in groups; average r over the group with the lowest q
        r=(b*q*var)
        low=np.isclose(q,q[0],rtol=1e-3)
        out_r=dict(N=N,bstd=b,ncfg=ncfg,q=q.tolist(),r=r.tolist(),r_lowest_group=float(r[low].mean()),
                   r_lowest_err=float(r[low].mean()*np.sqrt(2/(ncfg-1)/low.sum())),r_all_mean=float(r.mean()))
        res.append(out_r); print(json.dumps(dict((k,out_r[k]) for k in ('N','bstd','r_lowest_group','r_lowest_err','r_all_mean'))),flush=True)
        json.dump(res,open(out,'w'))
