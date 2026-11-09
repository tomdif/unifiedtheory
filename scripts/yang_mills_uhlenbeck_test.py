"""Lattice Uhlenbeck gauge, uniformity in n (numerics, not a proof).

Claim (ii) of the scale-invariant coercivity sketch: if the twisted Wilson action S = sum_p (1 - z P0) is below an
n-independent eps0, there is a gauge (background Landau to a flat vacuum, best center sector) with
E = <a, Delta_0 a> <= C S, a = log(U V^-1). Test: take heatbath configurations at beta_std, cool them step by step,
and at each step record (S, E). Reports E/S along the cooling paths, binned in S.
Written before any run: E/S <= about 2.4 (the inverse of the sphere profile S(R)/R^2 near R = 3) whenever S <= 2,
uniformly in n. Growth of E/S with n at fixed S would mean the Landau gauge is not uniformly good (Gribov or vortices).
Usage: out ns beta_std n_cfg
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np
from yang_mills_preconditioned_hessian import hessian, gauge_D, cool, gauge_fix
from yang_mills_twisted_step_scaling import twist, heat, over, staple, energy, qmul, qc

def qlog(q):
    w=np.clip(q[...,0],-1,1); s=np.linalg.norm(q[...,1:],axis=-1,keepdims=True); th=np.arctan2(s,w[...,None])
    return np.where(s>1e-14,th/np.maximum(s,1e-300),1.)*q[...,1:]

def act(U,z): return energy(U,z)*6*U.shape[1]**4/2   # energy = mean over planes of (2 - 2 z P0)
out=sys.argv[1]; ns=[int(x) for x in sys.argv[2].split(',')]; b=float(sys.argv[3]); ncfg=int(sys.argv[4]); res=[]
for N in ns:
    rng=np.random.default_rng(21+N); z=twist(N); par=np.indices((N,)*4).sum(0)%2
    V=np.zeros((4,)+(N,)*4+(4,)); V[...,0]=1
    for _ in range(100): heat(V,z,30.,rng,par); over(V,z,par)
    cool(V,z,par); D0=gauge_D(V); Delta0=(hessian(V,z,1.)+D0@D0.T).tocsr()
    U=V.copy()
    for _ in range(200): heat(U,z,b/2,rng,par); over(U,z,par)
    pts=[]
    for c in range(ncfg):
        for _ in range(30): heat(U,z,b/2,rng,par); over(U,z,par)
        W=U.copy()
        for step in range(400):
            for m in range(4):
                for p in (0,1):
                    A=staple(W,z,m); nrm=np.linalg.norm(A,axis=-1); mask=par==p
                    W[m][mask]=qc(A[mask]/nrm[mask][:,None])
            S=act(W,z)
            if S<3:
                best=None
                for c0 in (1,-1):
                    for c3 in (1,-1):
                        X=W.copy(); X[0][0]*=c0; X[3][:,:,:,0]*=c3; Xg,F=gauge_fix(X,V,par)
                        if best is None or F>best[1]: best=(Xg,F)
                a=np.stack([qlog(qmul(best[0][m],qc(V[m]))) for m in range(4)]).ravel()
                E=float(a@(Delta0@a)); pts.append((float(S),E)); print(json.dumps(dict(N=N,cfg=c,step=step,S=S,E=E,ratio=E/S)),flush=True)
            if S<0.05: break
    P=np.array(pts); bins=[(0,0.25),(0.25,0.5),(0.5,1),(1,2),(2,3)]
    summ={f'{lo}-{hi}':(float((P[(P[:,0]>=lo)&(P[:,0]<hi),1]/P[(P[:,0]>=lo)&(P[:,0]<hi),0]).max()) if ((P[:,0]>=lo)&(P[:,0]<hi)).any() else None) for lo,hi in bins}
    res.append(dict(N=N,points=pts,max_ratio_by_S=summ)); print(json.dumps(dict(N=N,max_ratio_by_S=summ)),flush=True); json.dump(res,open(out,'w'))
