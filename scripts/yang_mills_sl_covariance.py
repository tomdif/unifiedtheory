"""Stochastic-localization covariance along the path for 4D twisted SU(2) lattice Yang-Mills (numerics, not a proof).

The criterion. Links are unit quaternions in R^4. Stochastic localization tilts mu by <y, U>:
mu_t ∝ exp(sum_l <y_l, U_l>) mu, with y_t = t U* + B_t, U* ~ mu and B a Brownian motion.
- Then E[mu_t] = mu and Var_mu f = E Var_{mu_T} f + E int_0^T |Cov_{mu_t}(f, U)|^2 dt.
- Cauchy-Schwarz gives Var_mu f <= exp(int_0^T alpha_t dt) E Var_{mu_T} f, with alpha_t = ||Cov(mu_t)||_op.
- So a volume-uniform bound on alpha_t would give a volume-uniform Poincare inequality: a multiscale
  (Polchinski / Chen-Eldan) route to the gap with no Gaussian reference and no small fields.
- At t = 0, alpha = 1/4 exactly: gauge invariance kills every cross-link covariance.

What is measured. For each (beta_std, n, t), U* is thermalized and y = t U* + sqrt(t) xi is drawn. mu_t is sampled by
heat bath plus overrelaxation with the link field added to the staple field, starting from U*. U* is an exact posterior
sample (Nishimori; U* is gauge-randomized by Haar g_x, since thermalization from the twist-eater leaves the
long-wavelength gauge modes unmixed), so no burn-in is needed. alpha_t is estimated by split-sample PCA:
- the top covariance direction is found by power iteration on the samples of one chain;
- its variance is measured on a second, independent chain (same y, burn-in BURN sweeps).
(Interleaved halves of one chain share its noise; with d = 16 n^4 >> effective sample size, that inflated the
estimate to ~10 at t = 0, where the exact value is 1/4.)
This is an unbiased estimate of a lower bound on alpha_t.
Also reported: var_tr, the mean per-coordinate variance, and alpha_gauge, the largest variance over fixed unit
directions w_l = X_x U*_l - U*_l X_{x+mu} (gauge-orbit tangents at U*, X = e_a times 1, cos or sin of the lowest
momentum). These are the order parameters of a synchronization / Higgs transition, and their variance is exactly 1/4
at t = 0.
Written before any run: at beta_std = 2, alpha_t stays below 1 and flat in n for every t. At beta_std >= 6 there is a
window t ~ 0.5-3 where alpha_t grows with n: the synchronization / Higgs transition of the tilted model. That would
mean the plain covariance criterion fails at weak coupling.
Usage: out ns beta_stds ts n_samp sweeps_between
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np
from yang_mills_twisted_step_scaling import twist, heat, over, qmul, qc, staple, kp

def heat_t(U,z,beta,y,rng,par):
    for m in range(4):
        for p in (0,1):
            K=2*beta*qc(staple(U,z,m))+y[m]; nrm=np.linalg.norm(K,axis=-1); mask=(par==p)&(nrm>1e-12)
            a0=kp(nrm[mask],rng)
            v=rng.normal(size=(a0.size,3)); v/=np.linalg.norm(v,axis=-1,keepdims=True)
            q=np.concatenate([a0[:,None],np.sqrt(np.clip(1-a0**2,0,None))[:,None]*v],-1)
            U[m][mask]=qmul(q,K[mask]/nrm[mask][:,None])
def over_t(U,z,beta,y,par):
    for m in range(4):
        for p in (0,1):
            K=2*beta*qc(staple(U,z,m))+y[m]; nrm=np.linalg.norm(K,axis=-1); mask=(par==p)&(nrm>1e-12)
            d=K[mask]/nrm[mask][:,None]
            U[m][mask]=qmul(qmul(d,qc(U[m][mask])),d)

def gauge_random(U,rng):
    g=rng.normal(size=U.shape[1:]); g/=np.linalg.norm(g,axis=-1,keepdims=True)
    for m in range(4):
        U[m]=qmul(qmul(g,U[m]),qc(np.roll(g,-1,axis=m)))

out=sys.argv[1]; ns=[int(v) for v in sys.argv[2].split(',')]; bs=[float(v) for v in sys.argv[3].split(',')]
ts=[float(v) for v in sys.argv[4].split(',')]; ns_samp=int(sys.argv[5]); sw=int(sys.argv[6]); res=[]
BURN=int(os.environ.get('BURN','30'))
for N in ns:
    z=twist(N); par=np.indices((N,)*4).sum(0)%2
    x0=np.indices((N,)*4)[0]; fs=[np.ones((N,)*4),np.cos(2*np.pi*x0/N),np.sin(2*np.pi*x0/N)]
    for b in bs:
        rng=np.random.default_rng(1000*N+int(10*b)); beta=b/2
        Us=np.zeros((4,)+(N,)*4+(4,)); Us[...,0]=1; xx=np.indices((N,)*4)
        Us[1][xx[1]==0]=[0,1,0,0]; Us[2][xx[2]==0]=[0,0,1,0]
        for _ in range(200): heat(Us,z,beta,rng,par); over(Us,z,par); over(Us,z,par)
        gauge_random(Us,rng)          # mu is gauge invariant, so this makes U* an exact sample in the gauge sector too
        for t in ts:
            y=t*Us+np.sqrt(t)*rng.normal(size=Us.shape)
            def chain(seed):
                r=np.random.default_rng(seed); U=Us.copy(); X=[]
                for _ in range(BURN): heat_t(U,z,beta,y,r,par); over_t(U,z,beta,y,par); over_t(U,z,beta,y,par)
                for s_ in range(ns_samp):
                    for _ in range(sw): heat_t(U,z,beta,y,r,par); over_t(U,z,beta,y,par); over_t(U,z,beta,y,par)
                    X.append(U.ravel().copy())
                return np.array(X), U
            XA,_=chain(1); XB,U=chain(2)
            A=XA-XA.mean(0); B=XB-XB.mean(0); X=XB
            v=np.random.default_rng(0).normal(size=X.shape[1])
            for _ in range(60):
                v=A.T@(A@v); v/=np.linalg.norm(v)
            alpha=float(((B@v)**2).sum()/(len(B)-1)); alpha_in=float(((A@v)**2).sum()/(len(A)-1))
            var_tr=float((B**2).sum()/(len(B)-1)/X.shape[1])
            loc=v.reshape((4,)+(N,)*4+(4,)); w=np.linalg.norm(loc,axis=-1)**2
            ipr=float(1/(w**2).sum())                          # participation number of the top direction (links)
            # order-parameter directions: gauge-orbit tangents at U*, X = e_a f(x), f in {1, cos, sin of lowest k}
            ag=[]
            for f in fs:
                for a in range(1,4):
                    ea=np.zeros(4); ea[a]=1.
                    Xf=f[...,None]*ea
                    w=np.stack([qmul(Xf,Us[m])-qmul(Us[m],np.roll(Xf,-1,axis=m)) for m in range(4)]).ravel()
                    w/=np.linalg.norm(w); ag.append(float(((B@w)**2).sum()/(len(B)-1)))
            row=dict(N=N,bstd=b,t=t,alpha_gauge=max(ag),alpha_gauge_k0=max(ag[:3]),alpha_out=alpha,alpha_in=alpha_in,var_tr=var_tr,participation=ipr,
                     samples=ns_samp,sweeps=sw,overlap=float((U*Us).sum(-1).mean()))
            res.append(row); print(json.dumps(row),flush=True); json.dump(res,open(out,'w'))
