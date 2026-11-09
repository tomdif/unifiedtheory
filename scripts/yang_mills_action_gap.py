"""Action gap (ii') on the twisted lattice: search for non-vacuum critical points of small action (numerics, not a proof).

(ii') says every critical point of S = sum_p (1 - z P0) with S < eps0 is a vacuum, with eps0 independent of n. Search:
minimize G(U) = |grad S(U)|^2 (gradient along left perturbations exp(eps) U) with L-BFGS, from three kinds of start:
  cool  - heatbath at beta_std = 8, cooled until S < S_start;
  lump  - vacuum V times exp(a), a a random lump on a few neighboring links of size 0.5-2;
  wave  - vacuum times exp(a), a random smooth-ish field (random low Fourier modes).
A non-vacuum critical point shows up as G ~ 0 with S clearly > 0. Reports (S, G) at the end of each search.
Written before any run: every search with S < 2.5 ends at S ~ 0 (a vacuum) or at G clearly > 0. The smallest
non-vacuum critical value seen is >= the sphere barrier, about 4.75, and is n-independent.
Usage: out ns n_each
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, torch
from scipy.optimize import minimize
from yang_mills_preconditioned_hessian import cool
from yang_mills_twisted_step_scaling import twist, heat, over, staple, qc
torch.set_default_dtype(torch.float64); torch.set_num_threads(1)

def tq(a,b):
    w1,x1,y1,z1=a.unbind(-1); w2,x2,y2,z2=b.unbind(-1)
    return torch.stack([w1*w2-x1*x2-y1*y2-z1*z2,w1*x2+x1*w2+y1*z2-z1*y2,w1*y2-x1*z2+y1*w2+z1*x2,w1*z2+x1*y2-y1*x2+z1*w2],-1)
CJ=torch.tensor([1.,-1,-1,-1])
def texp(a):
    th=torch.sqrt((a*a).sum(-1,keepdim=True)+1e-300)
    return torch.cat([torch.cos(th),torch.where(th>1e-8,torch.sin(th)/th,1-th*th/6)*a],-1)
def action(U,zt):
    tot=0.
    for m in range(4):
        for n in range(m+1,4):
            P=tq(tq(tq(U[m],torch.roll(U[n],-1,m)),torch.roll(U[m],-1,n)*CJ),U[n]*CJ)
            tot=tot+(1-(zt if {m,n}=={1,2} else 1.)*P[...,0]).sum()
    return tot

out=sys.argv[1]; ns=[int(x) for x in sys.argv[2].split(',')]; k=int(sys.argv[3]); res=[]
for N in ns:
    rng=np.random.default_rng(41+N); z=twist(N); par=np.indices((N,)*4).sum(0)%2; zt=torch.tensor(z)
    V=np.zeros((4,)+(N,)*4+(4,)); V[...,0]=1
    for _ in range(100): heat(V,z,30.,rng,par); over(V,z,par)
    cool(V,z,par)
    def SG(U0):
        U0t=torch.tensor(U0)
        def f(x):
            a=torch.tensor(x,requires_grad=True)
            U=tq(texp(a.reshape(4,N,N,N,N,3)),U0t)
            eps=torch.zeros_like(a,requires_grad=True)
            S=action(tq(texp(eps.reshape(4,N,N,N,N,3)),U),zt)
            g,=torch.autograd.grad(S,eps,create_graph=True); G=(g*g).sum(); G.backward()
            return float(G.detach()),a.grad.numpy().copy()
        return f
    def Sof(U0,x):
        with torch.no_grad(): return float(action(tq(texp(torch.tensor(x).reshape(4,N,N,N,N,3)),torch.tensor(U0)),zt))
    starts=[]
    for i in range(k):   # cooled heatbath configurations, stopped at various S
        U=V.copy()
        for _ in range(60): heat(U,z,4.,rng,par); over(U,z,par)
        target=[5.,3.,2.,1.][i%4]
        for _ in range(2000):
            for m in range(4):
                for p in (0,1):
                    A=staple(U,z,m); nrm=np.linalg.norm(A,axis=-1); msk=par==p; U[m][msk]=qc(A[msk]/nrm[msk][:,None])
            if Sof(U,np.zeros(4*N**4*3))<target: break
        starts.append(('cool',U))
    for i in range(k):   # lumps
        a=np.zeros((4,)+(N,)*4+(3,)); x0=rng.integers(0,N,4)
        for j in range(3):
            mu=rng.integers(0,4); pos=tuple((x0+rng.integers(0,2,4))%N); a[(mu,)+pos]=rng.normal(size=3)*rng.uniform(0.3,1.5)
        starts.append(('lump',np.asarray(tq(texp(torch.tensor(a)),torch.tensor(V)))))
    for i in range(k):   # smooth waves
        c=np.indices((N,)*4)*2*np.pi/N; a=np.zeros((4,)+(N,)*4+(3,))
        for j in range(3):
            kk=rng.integers(-1,2,4); ph=rng.uniform(0,2*np.pi); amp=rng.normal(size=(4,3))*rng.uniform(0.05,0.25)
            a+=amp[:,None,None,None,None,:]*np.cos((kk[:,None,None,None,None]*c).sum(0)+ph)[None,...,None]
        starts.append(('wave',np.asarray(tq(texp(torch.tensor(a)),torch.tensor(V)))))
    for kind,U0 in starts:
        S0=Sof(U0,np.zeros(4*N**4*3))
        r=minimize(SG(U0),np.zeros(4*N**4*3),jac=True,method='L-BFGS-B',options=dict(maxiter=5000,gtol=1e-14,ftol=1e-20))
        row=dict(N=N,kind=kind,S_start=S0,S_end=Sof(U0,r.x),G_end=float(r.fun),it=int(r.nit))
        res.append(row); print(json.dumps(row),flush=True); json.dump(res,open(out,'w'))
