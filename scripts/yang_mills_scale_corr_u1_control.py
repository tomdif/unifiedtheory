"""Control for the scale-correlation test: is rho well below 1 in Coulomb U(1) physics or a measurement bug? (numerics, not a proof)

U(1) beta = 1.1 on N = 16 gave rho(2) = 0.06 and rho(4) = 0.00, where rho about 1 was predicted. Stated before this run:
  Exact Gaussian photon field through the same flow, density and estimator: rho = 1 within errors at L = 1, 2, 4. Otherwise the pipeline or r_free is wrong.
  Compact U(1) with beta rising: rho rises to 1, since monopoles die off. If so, beta = 1.1 reflects the non-Gaussian short-distance part of the action density,
  whose block variance falls like L^-4 against L^-8 for the free part, and r -> 0 does not separate a gapped theory from a massless one.
Result on N = 16: Gaussian rho = 1.00, 1.00, 0.98. rho rises to 1 with beta, but at beta = 1.5 rho(4) = 1.05 > rho(2) = 0.60, against the L^-4 scaling claimed above.
Stated before the N = 32 run: if beta = 1.1 is massless with a heavy short-distance part, rho(4) and rho(8) at N = 32 rise above rho(2). If they stay near 0, small r coexists with a massless theory out to L = 8.
Modes: gauss, out, N, n_samples; or compact, out, N, betas, seconds_per_beta. One Metropolis plus three overrelaxation sweeps per update.
"""
import os, sys, time, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
import numpy as np

EPS=0.05
def plaq(T,m,n): return T[m]+np.roll(T[n],-1,m)-np.roll(T[m],-1,n)-T[n]
def force(T,m):
    f=0.
    for n in range(4):
        if n==m: continue
        s=np.sin(plaq(T,m,n)); f=f+s-np.roll(s,1,n)
    return f
def flow(T,steps):
    for _ in range(steps): T=T-EPS*np.stack([force(T,m) for m in range(4)])
    return T
def dens(T):
    t=0.
    for m in range(4):
        for n in range(m+1,4): t=t+1-np.cos(plaq(T,m,n))
    return t
def staple(T,m):
    st=0.
    for n in range(4):
        if n==m: continue
        st=st+np.exp(1j*(np.roll(T[n],-1,m)-np.roll(T[m],-1,n)-T[n]))
        st=st+np.roll(np.exp(1j*(-np.roll(T[n],-1,m)-T[m]+T[n])),1,n)
    return st
def metro(T,beta,rng,par,step):
    for m in range(4):
        for p in (0,1):
            st=staple(T,m); d=rng.uniform(-step,step,T[m].shape)
            dS=beta*(np.real(np.exp(1j*(T[m]+d))*st)-np.real(np.exp(1j*T[m])*st))
            acc=(par==p)&(np.log(rng.random(T[m].shape))<dS)
            T[m][acc]=T[m][acc]+d[acc]
def over(T,par):
    for m in range(4):
        for p in (0,1):
            a=np.angle(staple(T,m)); mask=par==p
            T[m][mask]=(-2*a-T[m])[mask]
def blockavg(f,L):
    for ax in range(4):
        g=f.copy()
        for k in range(1,L): g=g+np.roll(f,-k,ax)
        f=g/L
    return f
def measure(T,Ls,rec):
    V=T; done=0
    for L in Ls:
        steps=int(round(L*L/8/EPS)); V=flow(V,steps-done); done=steps
        O=blockavg(dens(V),L)
        rec[L].append((float(O.mean()),float((O*O).mean()),float(np.mean([(O*np.roll(O,-2*L,ax)).mean() for ax in range(4)]))))
def summary(rec,Ls):
    out={}
    for L in Ls:
        a=np.array(rec[L]); B=25; idx=np.array_split(np.arange(len(a)),B)
        est=lambda x:(x[:,2].mean()-x[:,0].mean()**2)/(x[:,1].mean()-x[:,0].mean()**2)
        jk=np.array([est(np.delete(a,i,axis=0)) for i in idx])
        out[str(L)]=[float(est(a)),float(np.sqrt((B-1)*((jk-jk.mean())**2).mean()))]
    return out
def gauss(N,beta,rng):
    # Feynman gauge: <|A_m(k)|^2> = 1/(beta khat^2), zero mode dropped; F does not see the gauge.
    k=2*np.pi*np.fft.fftfreq(N); K=np.meshgrid(k,k,k,k,indexing='ij'); kh=sum(4*np.sin(q/2)**2 for q in K); kh[0,0,0,0]=np.inf
    return np.stack([np.fft.ifftn(np.fft.fftn(rng.normal(size=(N,)*4))/np.sqrt(beta*kh)).real for _ in range(4)])

mode,out,N=sys.argv[1],sys.argv[2],int(sys.argv[3]); Ls=[L for L in (1,2,4,8) if 4*L<=N]; res=[]
if mode=='gauss':
    rng=np.random.default_rng(N); rec={L:[] for L in Ls}; t0=time.time()
    for _ in range(int(sys.argv[4])): measure(gauss(N,1e4,rng),Ls,rec)
    res.append(dict(mode='gauss',N=N,n_meas=len(rec[1]),secs=time.time()-t0,by_L=summary(rec,Ls))); print(json.dumps(res[-1]),flush=True)
else:
    for beta in [float(b) for b in sys.argv[4].split(',')]:
        rng=np.random.default_rng(int(beta*1000)+N); par=np.indices((N,)*4).sum(0)%2; T=np.zeros((4,N,N,N,N)); step=1.2/np.sqrt(max(1.,beta))
        def upd():
            metro(T,beta,rng,par,step)
            for _ in range(3): over(T,par)
        for _ in range(300): upd()
        rec={L:[] for L in Ls}; tm=time.time()
        while time.time()-tm<float(sys.argv[5]):
            for _ in range(4): upd()
            measure(T,Ls,rec)
        res.append(dict(mode='compact',N=N,beta=beta,n_meas=len(rec[1]),by_L=summary(rec,Ls))); print(json.dumps(res[-1]),flush=True)
        json.dump(res,open(out,'w'),indent=1)
json.dump(res,open(out,'w'),indent=1)
