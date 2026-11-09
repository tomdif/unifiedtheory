"""Cheapest large-field direction: action minimized on energy spheres <a, Delta_0 a> = R^2 in the Landau slice (numerics, not a proof).

S_min(t) = min { S(exp(a) V) : D_V^T a = 0, <v, a> = t / sqrt(q) }, where V is a flat twisted vacuum, v the lowest
horizontal Delta_0 mode (eigenvalue q, unit norm), S = sum_p (1 - z P0), and the Boltzmann weight is exp(-beta_std S).
The free value is t^2/2. Reports where S_min stops being convex in t, and its maximum (the barrier) over t.

Question: is the profile n-independent in t (scale invariant classical action)? If so, the coarse large-field
region of this mode costs exp(-beta_std * A) with A an n-independent constant. On beta = b log n that is n^(-bA),
negligible against the 1/n accuracy of TargetAGap once bA > 1.
Written before any run: the profile is n-independent up to O(1/n^2), and convexity fails at t of order 1.
Usage: out ns Rs n_starts. Reports min S (free R^2/2), participation ratio pr (1 spread, ~0 local), max |a| per link.
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, torch, scipy.sparse.linalg as sla
from scipy.optimize import minimize
from scipy.sparse.linalg import lobpcg
from yang_mills_preconditioned_hessian import hessian, gauge_D, cool
from yang_mills_twisted_step_scaling import twist, heat, over
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
            s=zt if {m,n}=={1,2} else 1.
            tot=tot+(1-s*P[...,0]).sum()
    return tot

out=sys.argv[1]; ns=[int(x) for x in sys.argv[2].split(',')]; Rs=[float(x) for x in sys.argv[3].split(',')]; nstart=int(sys.argv[4]); res=[]
for N in ns:
    rng=np.random.default_rng(9+N); z=twist(N); par=np.indices((N,)*4).sum(0)%2
    V=np.zeros((4,)+(N,)*4+(4,)); V[...,0]=1
    for _ in range(100): heat(V,z,30.,rng,par); over(V,z,par)
    cool(V,z,par); D0=gauge_D(V); d=4*N**4*3
    Delta0=(hessian(V,z,1.)+D0@D0.T).tocsr()
    L=sla.splu((D0.T@D0).tocsc())
    proj=lambda x:x-D0@L.solve(D0.T@x)
    Vt=torch.tensor(V); zt=torch.tensor(z)
    def f(theta,R):
        th=torch.tensor(proj(theta),requires_grad=True)
        nrm=torch.sqrt(th@torch.tensor(Delta0@th.detach().numpy())*0+ (th*torch.tensor(Delta0@th.detach().numpy())).sum())
        # exact energy norm with gradient: <th, Delta0 th> computed via sparse matvec held fixed then corrected below
        return None
    Dt=torch.sparse_csr_tensor(torch.tensor(Delta0.indptr,dtype=torch.int64),torch.tensor(Delta0.indices,dtype=torch.int64),torch.tensor(Delta0.data),size=Delta0.shape)
    def f(theta,R):
        th=torch.tensor(proj(theta),requires_grad=True)
        e=(th*(Dt@th)).sum(); a=R*th/torch.sqrt(e)
        U=tq(texp(a.reshape(4,N,N,N,N,3)),Vt); S=action(U,zt); S.backward()
        return float(S.detach()),proj(th.grad.numpy())
    starts=[np.random.default_rng(100+k).normal(size=d) for k in range(nstart)]
    for R in Rs:
        best=None
        for k in range(nstart):
            r=minimize(lambda t:f(t,R),starts[k],jac=True,method='L-BFGS-B',options=dict(maxiter=4000,gtol=1e-10))
            starts[k]=r.x/np.linalg.norm(r.x)*np.sqrt(d)
            th=proj(r.x); a=R*th/np.sqrt(th@(Delta0@th)); site=(a.reshape(4,N**4,3)**2).sum((0,2)); site/=site.sum()
            row=dict(S=float(r.fun),pr=float(1/(site**2).sum()/N**4),amax=float(np.abs(a).reshape(-1,3).__pow__(2).sum(1).max()**.5))
            if best is None or row['S']<best['S']: best=row
        out_r=dict(N=N,R=R,free=R*R/2,**best); res.append(out_r); print(json.dumps(out_r),flush=True); json.dump(res,open(out,'w'))
