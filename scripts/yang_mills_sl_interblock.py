"""Inter-block coupling of the stochastic-localization posterior mu_t (numerics, not a proof).
The per-block soft variance is ~1 and n-independent (yang_mills_sl_tail.py), but the global operator norm at n = 4
was ~3: the blocks couple. Block-reduced estimator: chain A (pass 1) gives the top-k directions of each side-2
block; then chain A (pass 2) and an independent chain B record the projections onto all nb*k block directions.
The top eigenvector of the reduced covariance from A is scored by its variance on B (out-of-sample lower bound on
||Cov mu_t||_op). At n = 4 the full (unreduced) out-of-sample estimate is computed too, as calibration.
Written before any run: the reduced estimate at k = 8 recovers >= 80% of the full one at n = 4, and the reduced
operator norm is flat from n = 4 to 8 (within 30%), around 2.5-3.5 at beta_std = 8, t = 1.
Usage: out ns beta_std t R S k
"""
import os, sys, json; sys.path.insert(0, os.path.dirname(__file__))
import numpy as np
src=open(os.path.join(os.path.dirname(__file__),'yang_mills_sl_covariance.py')).read().split("out=sys.argv[1];")[0]
exec(src)
out=sys.argv[1]; ns=[int(x) for x in sys.argv[2].split(',')]; b=float(sys.argv[3]); t=float(sys.argv[4])
R=int(sys.argv[5]); S=int(sys.argv[6]); k=int(sys.argv[7]); beta=b/2; res=[]
def blocks_of(U,N):
    h=N//2; X=U.reshape(4,h,2,h,2,h,2,h,2,4).transpose(1,3,5,7,0,2,4,6,8,9)
    return X.reshape(h**4,-1)
def sweeps(U,z,y,rr,par,n):
    for _ in range(n): heat_t(U,z,beta,y,rr,par); over_t(U,z,beta,y,par); over_t(U,z,beta,y,par)
def top_oos(PA,PB):
    A=PA-PA.mean(0); B=PB-PB.mean(0)
    C=A.T@A/(len(A)-1); w,E=np.linalg.eigh(C); v=E[:,-1]
    return float(((B@v)**2).sum()/(len(B)-1)), float(w[-1])
for N in ns:
    z=twist(N); par=np.indices((N,)*4).sum(0)%2; nb=(N//2)**4
    for r in range(R):
        rng=np.random.default_rng(1000*N+r)
        Us=np.zeros((4,)+(N,)*4+(4,)); Us[...,0]=1; xx=np.indices((N,)*4); Us[1][xx[1]==0]=[0,1,0,0]; Us[2][xx[2]==0]=[0,0,1,0]
        for _ in range(150): heat(Us,z,beta,rng,par); over(Us,z,par); over(Us,z,par)
        gauge_random(Us,rng); y=t*Us+np.sqrt(t)*rng.normal(size=Us.shape)
        # pass 1 on chain A: block covariances
        rA=np.random.default_rng(10**6+1000*N+10*r+1); UA=Us.copy(); sweeps(UA,z,y,rA,par,30)
        m1=np.zeros((nb,256)); m2=np.zeros((nb,256,256))
        for _ in range(S):
            sweeps(UA,z,y,rA,par,3); X=blocks_of(UA,N); m1+=X; m2+=np.einsum('bi,bj->bij',X,X)
        m1/=S; C=m2/S-np.einsum('bi,bj->bij',m1,m1); del m2
        w,E=np.linalg.eigh(C); Vk=E[:,:,-k:]          # (nb,256,k)
        rB=np.random.default_rng(10**6+1000*N+10*r+2); UB=Us.copy(); sweeps(UB,z,y,rB,par,30)
        full=N==4; PA=[];PB=[];FA=[];FB=[]
        for _ in range(S):
            sweeps(UA,z,y,rA,par,3); sweeps(UB,z,y,rB,par,3)
            XA=blocks_of(UA,N); XB=blocks_of(UB,N)
            PA.append(np.einsum('bi,bik->bk',XA,Vk).ravel()); PB.append(np.einsum('bi,bik->bk',XB,Vk).ravel())
            if full: FA.append(UA.ravel().copy()); FB.append(UB.ravel().copy())
        red,red_in=top_oos(np.array(PA),np.array(PB))
        row=dict(N=N,r=r,bstd=b,t=t,S=S,k=k,reduced_oos=round(red,3),reduced_insample=round(red_in,3))
        if full:
            f,f_in=top_oos(np.array(FA),np.array(FB)); row.update(full_oos=round(f,3),full_insample=round(f_in,3))
        res.append(row); print(json.dumps(row),flush=True); json.dump(res,open(out,'w'))
