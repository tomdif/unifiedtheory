"""Scale correlation of a flowed gauge-invariant block observable, SU(2) and U(1) (numerics, not a proof).

Periodic torus, no twist. O_L(x) = average over a block of side L of the action density at Wilson flow time t = L^2/8.
r(L) = Cov(O_L(x), O_L(x + 2L e)) / Var(O_L), averaged over axes and sites, with 25-bin jackknife errors.
Stated before the run. The idea predicts:
  SU(2): r(L) falls with L at each beta, and points (r(L), r(2L)) from different beta lie on one decreasing curve below r(2L) = r(L).
  U(1): at beta = 1.1 (Coulomb) r(L) stays near a constant, so r(2L) is about r(L); at beta = 0.9 (confined) it falls.
Counts against it: SU(2) r(2L) >= r(L) at large L, or points from different beta that do not lie on one curve within errors.
One scale in the continuum forces r(L) = g(Lambda L), so collapse alone is weak evidence; r(2L) < r(L) is the content.
Added after launch and before any result was read: the exact free values (yang_mills_scale_corr_freegauge.py) rise with L at small L, and on
N = 16 the value at L = 4 is 0.076 against 0.030 at N = 48, because s = 2L is antipodal there. So raw r(2L) < r(L) cannot be the test on this lattice.
The test is rho(L) = r(L) / r_free(N, L). Coulomb U(1): rho about 1 at all L. SU(2): rho below 1 and falling with L. L = 4 on N = 16 is corrected only to leading order.
Usage: out group N betas seconds_per_beta. Beta is beta_std for SU(2).
"""
import os, sys, time, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0,os.path.dirname(__file__))
import numpy as np
from yang_mills_twisted_step_scaling import qmul,qc,S,staple,heat,over

EPS=0.05
def qexp(v):
    a=np.linalg.norm(v,axis=-1,keepdims=True); s=np.where(a>1e-12,np.sin(a)/np.maximum(a,1e-12),1.)
    return np.concatenate([np.cos(a),s*v],-1)
def flow_su2(U,z,steps):
    # dU/dt = -Im(U A) U has dA/dt = lap A at small field, so sqrt(8t) is the smoothing radius.
    for _ in range(steps):
        new=[]
        for m in range(4):
            c=qmul(U[m],staple(U,z,m)); new.append(qmul(qexp(-EPS*c[...,1:]),U[m]))
        U=np.stack(new)
    return U
def dens_su2(U):
    t=0.
    for m in range(4):
        for n in range(m+1,4):
            t=t+1-qmul(qmul(qmul(U[m],S(U[n],m)),qc(S(U[m],n))),qc(U[n]))[...,0]
    return t
def plaq_u1(T,m,n): return T[m]+np.roll(T[n],-1,m)-np.roll(T[m],-1,n)-T[n]
def force_u1(T,m):
    f=0.
    for n in range(4):
        if n==m: continue
        f=f+np.sin(plaq_u1(T,m,n))-np.roll(np.sin(plaq_u1(T,m,n)),1,n)
    return f
def flow_u1(T,steps):
    for _ in range(steps): T=T-EPS*np.stack([force_u1(T,m) for m in range(4)])
    return T
def dens_u1(T):
    t=0.
    for m in range(4):
        for n in range(m+1,4): t=t+1-np.cos(plaq_u1(T,m,n))
    return t
def metro_u1(T,beta,rng,par):
    for m in range(4):
        for p in (0,1):
            st=0.
            for n in range(4):
                if n==m: continue
                st=st+np.exp(1j*(np.roll(T[n],-1,m)-np.roll(T[m],-1,n)-T[n]))
                st=st+np.roll(np.exp(1j*(-np.roll(T[n],-1,m)-T[m]+T[n])),1,n)
            mask=par==p; d=rng.uniform(-1.,1.,T[m].shape)*1.2
            dS=beta*(np.real(np.exp(1j*(T[m]+d))*st)-np.real(np.exp(1j*T[m])*st))
            acc=mask&(np.log(rng.random(T[m].shape))<dS)
            T[m][acc]=T[m][acc]+d[acc]
def blockavg(f,L):
    for ax in range(4):
        g=f.copy()
        for k in range(1,L): g=g+np.roll(f,-k,ax)
        f=g/L
    return f

out,group,N,betas,secs=sys.argv[1],sys.argv[2],int(sys.argv[3]),[float(b) for b in sys.argv[4].split(',')],float(sys.argv[5])
Ls=[L for L in (1,2,4,8) if 4*L<=N]
res=[]
for bstd in betas:
    rng=np.random.default_rng(int(bstd*1000)+N); par=np.indices((N,)*4).sum(0)%2
    if group=='su2':
        U=np.zeros((4,N,N,N,N,4)); U[...,0]=1; z=np.ones((N,N,N,N)); beta=bstd/2
        upd=lambda: (heat(U,z,beta,rng,par),over(U,z,par),over(U,z,par))
    else:
        T=np.zeros((4,N,N,N,N)); upd=lambda: [metro_u1(T,bstd,rng,par) for _ in range(4)]
    t0=time.time()
    for _ in range(60 if N<=8 else 150): upd()
    rec={L:[] for L in Ls}; tm=time.time(); n=0
    while time.time()-tm<secs:
        for _ in range(4): upd()
        V=U if group=='su2' else T; done=0
        for L in Ls:
            steps=int(round(L*L/8/EPS)); V=flow_su2(V,z,steps-done) if group=='su2' else flow_u1(V,steps-done); done=steps
            O=blockavg(dens_su2(V) if group=='su2' else dens_u1(V),L)
            c0=float((O*O).mean()); cs=float(np.mean([(O*np.roll(O,-2*L,ax)).mean() for ax in range(4)]))
            rec[L].append((float(O.mean()),c0,cs))
        n+=1
    r=dict(group=group,N=N,beta=bstd,n_meas=n,therm_s=tm-t0,by_L={})
    for L in Ls:
        a=np.array(rec[L]); B=25
        idx=np.array_split(np.arange(len(a)),B)
        est=lambda x:(x[:,2].mean()-x[:,0].mean()**2)/(x[:,1].mean()-x[:,0].mean()**2)
        jk=np.array([est(np.delete(a,i,axis=0)) for i in idx])
        r['by_L'][str(L)]=[float(est(a)),float(np.sqrt((B-1)*((jk-jk.mean())**2).mean()))]
    res.append(r); print(json.dumps(r),flush=True); json.dump(res,open(out,'w'),indent=1)
