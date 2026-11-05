"""Tail over tilt realizations of the largest local soft-mode variance of mu_t (numerics, not a proof).
The stochastic-localization criterion needs ||Cov mu_t||_op bounded for (almost) every tilt y, not on average.
README ("Stochastic localization...") found the soft modes at t ~ 1 to be finite-range clusters, so the
operator norm is controlled by the worst side-2 block. For R independent (U*, y) realizations at each N, two
independent chains A, B accumulate per-block covariances online (memory O(blocks * 256^2)); the block's top
direction from A is scored by its variance under B (an out-of-sample lower bound, no top-eigenvalue
inflation). Reports the pooled per-block distribution (median, 99th percentile, max) and the per-realization
maximum, for each N.
Written before any run: per-block variance has an exponential-type tail, so the per-realization max grows like
log(#blocks), from ~1.3 (N=4) to ~1.6 (N=8) at beta_std = 8, t = 1; no realization exceeds 3.
Usage: out ns beta_std t R n_samp
"""
import os, sys, json; sys.path.insert(0, os.path.dirname(__file__))
import numpy as np
src=open(os.path.join(os.path.dirname(__file__),'yang_mills_sl_covariance.py')).read().split("out=sys.argv[1];")[0]
exec(src)
out=sys.argv[1]; ns=[int(x) for x in sys.argv[2].split(',')]; b=float(sys.argv[3]); t=float(sys.argv[4])
R=int(sys.argv[5]); S=int(sys.argv[6]); beta=b/2; res=[]
def blocks_of(U,N):
    # (nblocks, 256): links based in each side-2 block, 4 dirs x 16 sites x 4 comps
    h=N//2; X=U.reshape(4,h,2,h,2,h,2,h,2,4).transpose(1,3,5,7,0,2,4,6,8,9)
    return X.reshape(h**4,-1)
for N in ns:
    z=twist(N); par=np.indices((N,)*4).sum(0)%2; nb=(N//2)**4; per=[]
    for r in range(R):
        rng=np.random.default_rng(1000*N+r)
        Us=np.zeros((4,)+(N,)*4+(4,)); Us[...,0]=1; xx=np.indices((N,)*4); Us[1][xx[1]==0]=[0,1,0,0]; Us[2][xx[2]==0]=[0,0,1,0]
        for _ in range(150): heat(Us,z,beta,rng,par); over(Us,z,par); over(Us,z,par)
        gauge_random(Us,rng); y=t*Us+np.sqrt(t)*rng.normal(size=Us.shape)
        stats=[]
        for seed in (1,2):
            rr=np.random.default_rng(10**6+1000*N+10*r+seed); U=Us.copy()
            m1=np.zeros((nb,256)); m2=np.zeros((nb,256,256))
            for _ in range(30): heat_t(U,z,beta,y,rr,par); over_t(U,z,beta,y,par); over_t(U,z,beta,y,par)
            for s_ in range(S):
                for _ in range(3): heat_t(U,z,beta,y,rr,par); over_t(U,z,beta,y,par); over_t(U,z,beta,y,par)
                X=blocks_of(U,N); m1+=X; m2+=np.einsum('bi,bj->bij',X,X)
            m1/=S; stats.append((m2/S-np.einsum('bi,bj->bij',m1,m1))*S/(S-1))
        CA,CB=stats; w,E=np.linalg.eigh(CA); v=E[:,:,-1]
        loc=np.einsum('bi,bij,bj->b',v,CB,v); per.append(loc)
        print(json.dumps(dict(N=N,r=r,max=round(float(loc.max()),3),median=round(float(np.median(loc)),3))),flush=True)
    allv=np.concatenate(per); mx=np.array([p.max() for p in per])
    row=dict(N=N,bstd=b,t=t,R=R,S=S,blocks=nb,pooled_median=float(np.median(allv)),pooled_p99=float(np.quantile(allv,.99)),
             pooled_max=float(allv.max()),real_max_mean=float(mx.mean()),real_max_max=float(mx.max()),
             tail_frac_gt2=float((allv>2).mean()),tail_frac_gt1_5=float((allv>1.5).mean()))
    res.append(row); print(json.dumps(row),flush=True); json.dump(res,open(out,'w'))
