"""Long-lag Euclidean correlator of a Polyakov-loop observable (numerics, not a proof).

slow_lower_corr (TwistedSlowObservable.lean) gives the lower half of NeutralWindow from one neutral observable whose
connected correlator keeps C(n/a) >= delta C(0). The flowed plaquette density is a two-quantum composite spread up to
the flow cutoff, so at weak coupling almost none of its variance is slow. Here g = sum_{x2,x3} P1(x2,x3)^2, with P1 the
trace of the straight spatial line in direction 1 of the 3D-flowed slice. It is gauge invariant, neutral (a flip in
direction 1 changes the sign of every P1), and P1 is linear in the fluctuation around the traceless twisted holonomy.
Free-field estimate: the lowest neutral pair has energy 2 pi / n (momenta +-pi/n along the twisted direction 2), and its
weight is IR enhanced. So C(t)/C(0) should decay like e^{-2 pi t / n} with an O(1) prefactor, uniformly in n.
Written before any run: n * m_eff at lag ~ n/3 is bounded (between 3 and 15) at n = 6, 8, 10 and both betas, and
C(n/3)/C(0) does not fall with n. A fall of C(n/3)/C(0) with n at fixed beta would mean the slow weight vanishes.
ADM=eps (env, 2026-11-04): Luscher admissibility, the Wilson measure restricted to configurations with every plaquette
a_p = 1 - z tr(P)/2 < eps. Heat-bath and overrelaxation proposals are accepted only if all six plaquettes of the link
stay below eps; same-direction same-parity links share no plaquette, so this is exact Metropolis for the restricted
measure. Purpose: decoupling test. If C(n/3)/C(0) is unchanged (beyond the small coupling shift) when the large-field
plaquettes a_p >= eps* ~ 0.27 are removed, then large-field regions do not carry the neutral slow weight.
Written before the ADM runs: at n = 6, beta_std = 4 and 6, the ADM = 0.27 and 0.5 values of C(n/3)/C(0), averaged over
the three directions, agree with Wilson within 0.03.
Usage: out ns betas ncfg   (env TFAC time extent factor, default 3; FLOWC flow t = n^2/FLOWC, default 32)
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, torch
from yang_mills_twisted_step_scaling import heat, over, staple, kp, qmul, qc
def zz4(z,m,k): return z if {m,k}=={1,2} else 1.
def link_maxplaq(U,z,m):
    """For every link in direction m: the largest action among its six plaquettes."""
    M=None
    for k in range(4):
        if k==m: continue
        P=qmul(qmul(qmul(U[m],np.roll(U[k],-1,m)),qc(np.roll(U[m],-1,k))),qc(U[k]))
        a=1-zz4(z,m,k)*P[...,0]; a2=np.maximum(a,np.roll(a,1,k))
        M=a2 if M is None else np.maximum(M,a2)
    return M
ADM=float(os.environ.get('ADM','0')); acc_stats=[0,0]
def adm_update(U,z,beta,rng,par,kind):
    for m in range(4):
        for p in (0,1):
            A=staple(U,z,m); nrm=np.linalg.norm(A,axis=-1); mask=(par==p)&(nrm>1e-12)
            old=U[m].copy()
            if kind=='heat':
                a0=kp(2*beta*nrm[mask],rng)
                v=rng.normal(size=(a0.size,3)); v/=np.linalg.norm(v,axis=-1,keepdims=True)
                q=np.concatenate([a0[:,None],np.sqrt(np.clip(1-a0**2,0,None))[:,None]*v],-1)
                U[m][mask]=qmul(q,qc(A[mask]/nrm[mask][:,None]))
            else:
                Ah=qc(A[mask]/nrm[mask][:,None]); U[m][mask]=qmul(qmul(Ah,qc(U[m][mask])),Ah)
            bad=mask&(link_maxplaq(U,z,m)>=ADM)
            U[m][bad]=old[bad]; acc_stats[0]+=int(mask.sum()-bad.sum()); acc_stats[1]+=int(mask.sum())
if ADM>0:
    def heat(U,z,beta,rng,par): adm_update(U,z,beta,rng,par,'heat')
    def over(U,z,par): adm_update(U,z,None,None,par,'over')
torch.set_default_dtype(torch.float64); torch.set_num_threads(1)

def tq(a,b):
    w1,x1,y1,z1=a.unbind(-1); w2,x2,y2,z2=b.unbind(-1)
    return torch.stack([w1*w2-x1*x2-y1*y2-z1*z2,w1*x2+x1*w2+y1*z2-z1*y2,w1*y2-x1*z2+y1*w2+z1*x2,w1*z2+x1*y2-y1*x2+z1*w2],-1)
CJ=torch.tensor([1.,-1,-1,-1])
def texp(a):
    th=torch.sqrt((a*a).sum(-1,keepdim=True)+1e-300)
    return torch.cat([torch.cos(th),torch.where(th>1e-8,torch.sin(th)/th,1-th*th/6)*a],-1)
def S3(U,zt):
    s=0.
    for m in range(3):
        for k in range(m+1,3):
            P=tq(tq(tq(U[m],torch.roll(U[k],-1,m)),torch.roll(U[m],-1,k)*CJ),U[k]*CJ)
            s=s+(1-(zt if (m,k)==(0,1) else 1.)*P[...,0]).sum()
    return s
def flow(U,zt,t,eps=0.02):
    for _ in range(int(round(t/eps))):
        w=torch.zeros(U.shape[:-1]+(3,),requires_grad=True)
        G,=torch.autograd.grad(S3(tq(texp(w),U),zt),w)
        U=tq(texp(-eps*G),U).detach()
    return U
def lines(U,m):
    """Trace/2 of the straight line in spatial direction m (axis m of the slice), as a function of the other two."""
    L=U[m].select(m,0)
    for x in range(1,U.shape[1]): L=tq(L,U[m].select(m,x))
    return L[...,0]

out=sys.argv[1]; ns=[int(x) for x in sys.argv[2].split(',')]; betas=[float(x) for x in sys.argv[3].split(',')]
ncfg=int(sys.argv[4]); fc=float(os.environ.get('FLOWC','32')); res=[]
for N in ns:
    Lt=int(os.environ.get('TFAC','3'))*N; shp=(Lt,N,N,N)
    z=np.ones(shp); z[:,0,0,:]=-1; par=np.indices(shp).sum(0)%2; zt=torch.tensor(z[0])
    for bs in betas:
        rng=np.random.default_rng(int(100*bs)+N+11+int(os.environ.get('SEED','0')))
        U4=np.zeros((4,)+shp+(4,)); U4[...,0]=1
        if not os.environ.get('COLD'):   # flat twist-eating start (U=1 is not a vacuum of the twisted action)
            xx=np.indices(shp); U4[1][xx[1]==0]=[0,1,0,0]; U4[2][xx[2]==0]=[0,0,1,0]
        for _ in range(200): heat(U4,z,bs/2,rng,par); over(U4,z,par)
        rows={k:[] for k in ('P1sq','P2sq','P3sq')}
        for c in range(ncfg):
            for _ in range(10): heat(U4,z,bs/2,rng,par); over(U4,z,par)
            acc={k:[] for k in rows}
            for t0 in range(Lt):
                V=flow(torch.tensor(U4[1:,t0]),zt,N*N/fc) if fc>0 else torch.tensor(U4[1:,t0])
                for m,k in enumerate(('P1sq','P2sq','P3sq')): acc[k].append(float((lines(V,m)**2).sum()))
            for k in rows: rows[k].append(acc[k])
        row=dict(N=N,beta_std=bs,Lt=Lt,flowc=fc,cfgs=ncfg,adm=ADM,acc=acc_stats[0]/max(acc_stats[1],1))
        acc_stats[0]=acc_stats[1]=0
        for k in rows:
            A=np.array(rows[k]); A=A-A.mean()
            C=np.array([(A*np.roll(A,-s,1)).mean() for s in range(Lt//2+1)])
            ts=max(1,round(N/3)); Cn=C/C[0]
            # jackknife error on C(n/3)/C(0)
            jk=[]
            for i in range(len(A)):
                B=np.delete(A,i,0); jk.append((B*np.roll(B,-ts,1)).mean()/(B*B).mean())
            jk=np.array(jk)
            row[k]=dict(Cn=[round(float(x),3) for x in Cn],t_star=ts,C_tstar=float(Cn[ts]),
                        err=float(np.sqrt((len(A)-1)*((jk-jk.mean())**2).mean())),
                        n_meff=float(-np.log(Cn[ts])*N/ts) if Cn[ts]>0 else None,raw=rows[k])
        res.append(row); print(json.dumps({k:({kk:vv for kk,vv in v.items() if kk!='raw'} if isinstance(v,dict) else v)
                                           for k,v in row.items()}),flush=True); json.dump(res,open(out,'w'))
