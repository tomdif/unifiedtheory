"""Is compact U(1) at beta = 1.1 massless, and why is its scale correlation r near 0? (numerics, not a proof)

G(k) = beta * <|F_mn(k)|^2> / V at k along m, F = sin P after flow t = 1/4, with the free flow factor removed. Free photon: G = 1 for all k, massless with renormalized
coupling: G constant as k -> 0, Debye-screened: G ~ k^2 / (k^2 + m^2) -> 0.
Stated before the run. Massless at beta = 1.1 and 1.5 from hot and cold starts: G(k) flat to within 15% over the two lowest k. Confined at 0.9: G(k1) well below G(k4).
If beta = 1.1 is massless, its small r has one of two causes, read from Var(O_2) beta^2 and Cov(O_2, O_2 shifted 2L) beta^2 against beta = 8: Var far above free (short-range noise), or Cov far below free.
Usage: out N seconds; each case is (beta, start).
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
    return sum(1-np.cos(plaq(T,m,n)) for m in range(4) for n in range(m+1,4))
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
            acc=(par==p)&(np.log(rng.random(T[m].shape))<dS); T[m][acc]=T[m][acc]+d[acc]
def over(T,par):
    for m in range(4):
        for p in (0,1):
            a=np.angle(staple(T,m)); mask=par==p; T[m][mask]=(-2*a-T[m])[mask]
def blockavg(f,L):
    for ax in range(4):
        g=f.copy()
        for k in range(1,L): g=g+np.roll(f,-k,ax)
        f=g/L
    return f
out,N,secs=sys.argv[1],int(sys.argv[2]),float(sys.argv[3]); res=[]; t=0.25; steps=int(round(t/EPS)); K=[1,2,3,4,N//2]
for beta,start in ((0.9,'hot'),(1.1,'cold'),(1.1,'hot'),(1.5,'cold'),(8.,'cold')):
    rng=np.random.default_rng(int(beta*100)+(start=='hot')); par=np.indices((N,)*4).sum(0)%2
    T=rng.uniform(-np.pi,np.pi,(4,N,N,N,N)) if start=='hot' else np.zeros((4,N,N,N,N)); step=1.2/np.sqrt(max(1.,beta))
    def upd():
        metro(T,beta,rng,par,step)
        for _ in range(3): over(T,par)
    for _ in range(300): upd()
    rows=[]; plaqs=[]; tm=time.time()
    while time.time()-tm<secs:
        for _ in range(4): upd()
        plaqs.append(float(np.mean([np.cos(plaq(T,m,n)).mean() for m in range(4) for n in range(m+1,4)])))
        V=flow(T,steps); G=np.zeros(len(K))
        for m in range(4):
            for n in range(4):
                if n==m: continue
                F=np.fft.fft(np.sin(plaq(V,m,n)),axis=m)
                F=np.moveaxis(F,m,0)
                s=(np.abs(F.sum(axis=(1,2,3)))**2)/N**4
                G+=np.array([s[j]*np.exp(2*t*4*np.sin(np.pi*j/N)**2) for j in K])
        V2=flow(V,int(round(0.5/EPS))-steps); O=blockavg(dens(V2),2)
        rows.append(list(beta*G/12)+[float(O.mean()),float((O*O).mean()),float(np.mean([(O*np.roll(O,-4,ax)).mean() for ax in range(4)]))])
    a=np.array(rows); bins=np.array([x.mean(0) for x in np.array_split(a,20)])
    v=(a[:,len(K)+1].mean()-a[:,len(K)].mean()**2)*beta**2; c=(a[:,len(K)+2].mean()-a[:,len(K)].mean()**2)*beta**2
    r=dict(beta=beta,start=start,N=N,n=len(a),plaq=float(np.mean(plaqs)),k=K,G=bins[:,:len(K)].mean(0).tolist(),G_err=(bins[:,:len(K)].std(0,ddof=1)/np.sqrt(20)).tolist(),var_beta2=float(v),cov_beta2=float(c))
    print(json.dumps(r),flush=True); res.append(r); json.dump(res,open(out,'w'),indent=1)
