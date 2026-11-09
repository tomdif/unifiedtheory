"""Neutral gap with the twist on a T^2 of side L and two longer directions, as L crosses 1/Lambda (numerics, not a proof).

Lattice N0 x L x L x N3, N0 = N3 = 3L, SU(2) Wilson, twist n12 = 1 as in yang_mills_twisted_step_scaling.py. Transfer direction 0. Neutral zero-momentum slice operators built from APE-smeared
spatial links with center signs: (tr W1)^2 + (tr W2)^2, Q12, Q13 + Q23, at two smearing levels. Lowest level from a 2-to-t GEVP, connected, delete-one-bin jackknife. Effective masses are upper bounds on the lowest coupled level.
This asks whether adiabatic continuity in L looks plausible, the first test of the R^2 x T^2 idea. WRITTEN BEFORE ANY RUN:
  Control: beta_std = 32, E L within 30% of the tree value 4 L asinh(sin(pi/(2L))). Otherwise the pipeline is not valid and nothing below counts.
  Kills the idea: at beta_std 2.4 or 2.5, any L with E / sqrt(sigma) < 1 at more than 3 sigma, using sqrt(sigma) a = 0.27, 0.18 (recalled, not measured here), a level far below the expected glueball value of about 3.5 and the tree value 2 pi / (L sqrt(sigma)).
  Encouraging only: E / sqrt(sigma) falling smoothly from the tree value toward a plateau. A weak transition could hide at this resolution, and masses here are upper bounds. This says nothing about a proof.
Usage: out; runs the list in PLAN as (beta_std, L, seconds).
"""
import os, sys, time, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0,os.path.dirname(__file__))
import numpy as np, scipy.linalg as sl
from yang_mills_twisted_step_scaling import qmul,qc,S,zz,heat,over

PLAN=[(32.,4,300),(32.,6,600),(2.5,4,420),(2.5,6,600),(2.5,8,900),(2.5,12,2400),(2.4,4,420),(2.4,6,600),(2.4,8,900)]
def setup(L):
    sh=(3*L,L,L,3*L); z=np.ones(sh); z[:,0,0,:]=-1
    U=np.zeros((4,)+sh+(4,)); U[...,0]=1; U[1][:,0,:,:]=np.array([0.,1,0,0]); U[2][:,:,0,:]=np.array([0.,0,1,0])
    return U,z,np.indices(sh).sum(0)%2
def ape(U,z,n,rho=0.25):
    for _ in range(n):
        new=U.copy()
        for m in (1,2,3):
            A=0.
            for k in (1,2,3):
                if k==m: continue
                s=zz(z,m,k)
                up=qmul(qmul(S(U[k],m),qc(S(U[m],k))),qc(U[k])); bk=qmul(qmul(qc(S(U[k],m)),qc(U[m])),U[k])
                if not np.isscalar(s): up=up*s[...,None]; bk=bk*s[...,None]
                A=A+up+S(bk,k,-1)
            V=U[m]+rho*qc(A); new[m]=V/np.linalg.norm(V,axis=-1,keepdims=True)
        U=new
    return U
def slices(U,z,L):
    W=[]
    for m in (1,2):
        P=U[m].copy(); q=U[m]
        for j in range(1,L): q=S(q,m); P=qmul(P,q)
        W.append(4*P[...,0]**2)
    ax=(1,2,3); L12=(W[0]+W[1]).mean(ax)
    def Q(m,n):
        P=qmul(qmul(qmul(U[m],S(U[n],m)),qc(S(U[m],n))),qc(U[n]))[...,0]; s=zz(z,m,n)
        return (s*P).mean(ax)
    return [L12,Q(1,2),Q(1,3)+Q(2,3)]
def analyze(X,T,nb=20):
    # X: meas x ops x T; correlators of connected ops, symmetrized in tau
    n=X.shape[0]; idx=np.array_split(np.arange(n),nb)
    def corr(sel):
        Y=X[sel]; Y=Y-Y.mean((0,2),keepdims=True); F=np.fft.rfft(Y,axis=2)
        C=np.fft.irfft(np.einsum('nit,njt->ijt',F,F.conj()),T,axis=2)/(len(sel)*T)
        return 0.5*(C+np.transpose(np.roll(C[...,::-1],1,axis=2),(1,0,2)))
    def E(C,t0=1):
        out=[]
        A=C[...,t0]; A=0.5*(A+A.T)
        w,V=np.linalg.eigh(A); keep=w>w.max()*1e-3; B=V[:,keep]/np.sqrt(w[keep])
        for t in range(t0,5):
            M=lambda s:B.T@(0.5*(C[...,s]+C[...,s].T))@B
            a=np.linalg.eigvalsh(M(t)).max(); b=np.linalg.eigvalsh(M(t+1)).max()
            out.append(np.log(a/b) if a>0 and b>0 else np.nan)
        return out
    full=np.array(E(corr(np.arange(n))))
    jk=np.array([E(corr(np.concatenate([idx[j] for j in range(nb) if j!=i]))) for i in range(nb)])
    err=np.sqrt((nb-1)*np.nanmean((jk-np.nanmean(jk,0))**2,0))
    return full.tolist(),err.tolist()
def run(bstd,L,secs,rng):
    U,z,par=setup(L); beta=bstd/2; T=3*L; lv=[max(1,round((L/4)**2)),max(2,round((0.45*L)**2))]
    def upd():
        heat(U,z,beta,rng,par); over(U,z,par); over(U,z,par); over(U,z,par)
    for _ in range(100): upd()
    rec=[]; tm=time.time()
    while time.time()-tm<secs:
        upd(); upd()
        V=ape(U,z,lv[0]); ops=slices(V,z,L); V=ape(V,z,lv[1]-lv[0]); ops+=slices(V,z,L)
        rec.append(np.array(ops))
    X=np.array(rec); E,err=analyze(X,T)
    tree=4*L*np.arcsinh(np.sin(np.pi/(2*L)))
    return dict(beta_std=bstd,L=L,T=T,n=len(rec),tau=[1,2,3,4],E=E,err=err,EL_tree=float(tree))
if __name__=='__main__':
    out=sys.argv[1]; res=[]; plan=PLAN if len(sys.argv)<3 else json.loads(sys.argv[2])
    for bstd,L,secs in plan:
        r=run(bstd,L,secs,np.random.default_rng(int(bstd*10)+L)); res.append(r); print(json.dumps(r),flush=True); json.dump(res,open(out,'w'),indent=1)
