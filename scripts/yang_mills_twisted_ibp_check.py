"""Heatbath check of TwistedIBP.gibbs_ibp: E[S1^2] = E[S2] along exp(tX)U (numerics, not a proof).

S1, S2 are central finite differences of the full action S = beta sum (2 - 2 z Re P), with X a single link and a
random colour, and with X a random field. Reports both sides, jackknife errors, and 48 beta |X|^2 from force_bound.
"""
import os, sys
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='2'
sys.path.insert(0,os.path.dirname(__file__))
import numpy as np, json
from yang_mills_twisted_step_scaling import qmul,qc,S as sh,twist,zz,heat,over

def action(U,z,beta):
    tot=0.
    for m in range(4):
        for n in range(m+1,4):
            P=qmul(qmul(qmul(U[m],sh(U[n],m)),qc(sh(U[m],n))),qc(U[n]))
            tot+=(2-2*zz(z,m,n)*P[...,0]).sum()
    return beta*tot
def qexp(v):
    r=np.linalg.norm(v,axis=-1,keepdims=True)
    return np.concatenate([np.cos(r),np.sinc(r/np.pi)*v],-1)

N=4; res=[]; h=1e-3
for bstd in (2.,4.,8.):
    beta=bstd/2; rng=np.random.default_rng(int(bstd)); z=twist(N); par=np.indices((N,)*4).sum(0)%2
    U=np.zeros((4,N,N,N,N,4)); U[...,0]=1
    U[1][:,0,:,:]=np.array([0.,1,0,0]); U[2][:,:,0,:]=np.array([0.,0,1,0])
    for _ in range(100):
        heat(U,z,beta,rng,par); over(U,z,par)
    rec={'link':[],'field':[]}
    for _ in range(int(sys.argv[2])):
        heat(U,z,beta,rng,par); over(U,z,par)
        for kind in rec:
            X=np.zeros(U.shape[:-1]+(3,))
            if kind=='link':
                i=tuple(rng.integers(0,[4,N,N,N,N])); X[i][rng.integers(3)]=1.
            else:
                X=rng.normal(size=X.shape)
            w=(X**2).sum()
            s0=action(U,z,beta); sp=action(qmul(qexp(h*X),U),z,beta); sm=action(qmul(qexp(-h*X),U),z,beta)
            rec[kind].append(((sp-sm)/(2*h),(sp+sm-2*s0)/h**2,w))
    for kind,v in rec.items():
        a=np.array(v); lhs=a[:,0]**2/a[:,2]; rhs=a[:,1]/a[:,2]; n=len(a)
        e=lambda x:float(x.std(ddof=1)/np.sqrt(n))
        r=dict(beta_std=bstd,X=kind,n=n,E_S1sq_per_W=float(lhs.mean()),err1=e(lhs),E_S2_per_W=float(rhs.mean()),err2=e(rhs),bound_48beta=48*beta,diff=float((lhs-rhs).mean()),diff_err=e(lhs-rhs))
        res.append(r); print(json.dumps(r),flush=True)
json.dump(res,open(sys.argv[1],'w'),indent=1)
