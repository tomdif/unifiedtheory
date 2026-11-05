"""One renormalization step as a Schur complement (numerics, not a proof).

Exact inequality (by hand, README "One RG step as a Schur complement"): split the field into fine x and coarse y with
coarse marginal exp(-U_eff(y)) = int exp(-U(x,y)) dx. Then Hess U_eff = E[H_yy | y] - Cov(grad_y U | y), and where the
fine block is convex (H_xx > 0) Brascamp-Lieb bounds the covariance, so
    Hess U_eff(y) >= E[ H_yy - H_yx H_xx^{-1} H_xy | y ].
So one step preserves convexity if (a) the fine block is convex and (b) the AVERAGED Schur complement is positive on the
coarse modes. The bare Hessian is soft pointwise at long wavelength (yang_mills_preconditioned_hessian.py); this
measures whether the average of the Schur complement is.

Coarse = the m lowest horizontal modes of the flat twisted Hodge Laplacian Delta_0 at a cooled vacuum V; fine = the
orthogonal complement. Configurations: twisted heatbath, background Landau gauge to V (best of four center sectors).
H = Hess(beta_std) + K beta_std D_V D_V^T (restriction to the background-gauge slice), optionally + 2 I (Ricci of SU(2) per link).
Reported, normalized by beta_std q on the coarse modes (free field = 1):
  mu_f   = lowest eigenvalue of H_ff against beta_std Delta_0 on the fine space (hypothesis (a));
  sig_pt = lowest eigenvalue of the Schur complement, per configuration (pointwise);
  sig_av = lowest eigenvalue of the configuration-averaged Schur complement (hypothesis (b));
  bare   = lowest eigenvalue of the configuration-averaged H_cc (no Schur subtraction).
Written before any run: sig_pt is soft and falls with n; sig_av stays >= 0.7 and flat in n = 4, 6, 8. sig_av <= 0, or
sig_av falling with n like sig_pt, kills this one-step route.
Usage: out ns beta_stds n_cfg n_modes [ric 0/1]
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, scipy.sparse as sp
from scipy.sparse.linalg import lobpcg, LinearOperator, cg
from yang_mills_preconditioned_hessian import hessian, gauge_D, cool, gauge_fix
from yang_mills_twisted_step_scaling import twist, heat, over

out=sys.argv[1]; ns=[int(x) for x in sys.argv[2].split(',')]; bs=[float(x) for x in sys.argv[3].split(',')]
ncfg=int(sys.argv[4]); nm=int(sys.argv[5]); ric=len(sys.argv)>6 and sys.argv[6]=='1'; K=100.; res=[]
for N in ns:
    rng=np.random.default_rng(11+N); z=twist(N); par=np.indices((N,)*4).sum(0)%2
    V=np.zeros((4,)+(N,)*4+(4,)); V[...,0]=1
    for _ in range(100): heat(V,z,30.,rng,par); over(V,z,par)
    cool(V,z,par); D0=gauge_D(V); Delta0=(hessian(V,z,1.)+D0@D0.T).tocsr(); d=Delta0.shape[0]
    Pv=(hessian(V,z,1.)+K*D0@D0.T).tocsr()
    q,E=lobpcg(Pv,np.random.default_rng(3).normal(size=(d,nm)),largest=False,tol=1e-9,maxiter=3000)
    o=np.argsort(q); q=q[o]; E=E[:,o]; E,_=np.linalg.qr(E)
    print('N',N,'coarse q',np.round(q,4).tolist(),flush=True)
    Pf=lambda x: x-E@(E.T@x)
    Mf=LinearOperator((d,d),matvec=lambda x: Pf(Pv@Pf(x))+E@(E.T@x),dtype=float)   # Delta_0 (horizontal) on fine, I on coarse
    for b in bs:
        U=V.copy()
        for _ in range(300): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
        Ss=[]; Hcc=[]; muf=[]; sig_pt=[]
        for c in range(ncfg):
            for _ in range(20): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
            best=None
            for c0 in (1,-1):
                for c3 in (1,-1):
                    W=U.copy(); W[0][0]*=c0; W[3][:,:,:,0]*=c3; Wg,F=gauge_fix(W,V,par)
                    if best is None or F>best[1]: best=(Wg,F)
            Ug=best[0]   # background Landau slice D_V^T a = 0: penalize vertical directions of V, not of U
            H=(hessian(Ug,z,b)+K*b*D0@D0.T).tocsr()
            if ric: H=H+2*sp.identity(d,format='csr')
            Hff=LinearOperator((d,d),matvec=lambda x: Pf(H@Pf(x))+b*E@(E.T@x),dtype=float)
            # (a) fine convexity relative to beta Delta_0
            w,_=lobpcg(Hff,np.random.default_rng(c).normal(size=(d,4)),B=Mf,largest=False,tol=1e-6,maxiter=800)
            mu=float(w.min())/b; muf.append(mu)
            HE=H@E; hcc=E.T@HE; Hcc.append(hcc)
            if mu<=0:
                sig_pt.append(None); Ss.append(None); continue
            X=np.zeros_like(E)
            for i in range(nm):
                rhs=Pf(HE[:,i]); x,info=cg(Hff,rhs,rtol=1e-10,maxiter=5000); X[:,i]=Pf(x)
            Sc=hcc-HE.T@X; Sc=(Sc+Sc.T)/2; Ss.append(Sc)
            nq=np.diag(1/np.sqrt(b*q))
            sig_pt.append(float(np.linalg.eigvalsh(nq@Sc@nq)[0]))
            print(json.dumps(dict(N=N,bstd=b,cfg=c,mu_f=mu,sig_pt=sig_pt[-1])),flush=True)
        nq=np.diag(1/np.sqrt(b*q)); good=[S for S in Ss if S is not None]
        row=dict(N=N,bstd=b,ric=ric,nm=nm,q=q.tolist(),mu_f=muf,mu_f_min=min(muf),sig_pt=sig_pt,
                 sig_av=float(np.linalg.eigvalsh(nq@np.mean(good,0)@nq)[0]) if good else None,
                 bare=float(np.linalg.eigvalsh(nq@np.mean(Hcc,0)@nq)[0]),n_fine_convex=len(good))
        res.append(row); print(json.dumps({k:v for k,v in row.items() if k not in ('q','mu_f','sig_pt')}),flush=True)
        json.dump(res,open(out,'w'))
