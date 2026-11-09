"""Classical large-field profile along the lowest twisted mode (numerics, not a proof).

S_min(t) = min { S(exp(a) V) : D_V^T a = 0, <v, a> = t / sqrt(q) }, where V is a flat twisted vacuum, v the lowest
horizontal Delta_0 mode (eigenvalue q, unit norm), S = sum_p (1 - z P0), and the Boltzmann weight is exp(-beta_std S).
The free value is t^2/2. Reports where S_min stops being convex in t, and its maximum (the barrier) over t.

Question: is the profile n-independent in t (scale invariant classical action)? If so, the coarse large-field
region of this mode costs exp(-beta_std * A) with A an n-independent constant. On beta = b log n that is n^(-bA),
negligible against the 1/n accuracy of TargetAGap once bA > 1.
Written before any run: the profile is n-independent up to O(1/n^2), and convexity fails at t of order 1.
Usage: out ns t_max n_t
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

out=sys.argv[1]; ns=[int(x) for x in sys.argv[2].split(',')]; tmax=float(sys.argv[3]); nt=int(sys.argv[4]); res=[]
for N in ns:
    rng=np.random.default_rng(9+N); z=twist(N); par=np.indices((N,)*4).sum(0)%2
    V=np.zeros((4,)+(N,)*4+(4,)); V[...,0]=1
    for _ in range(100): heat(V,z,30.,rng,par); over(V,z,par)
    cool(V,z,par); D0=gauge_D(V); d=4*N**4*3
    Pm=(hessian(V,z,1.)+100*D0@D0.T).tocsr()
    q,E=lobpcg(Pm,np.random.default_rng(3).normal(size=(d,4)),largest=False,tol=1e-10,maxiter=3000)
    v=E[:,np.argmin(q)]; q=float(q.min()); v/=np.linalg.norm(v)
    L=sla.splu((D0.T@D0).tocsc())
    def proj(x):   # onto ker D0^T, then remove the v component
        x=x-D0@L.solve(D0.T@x); return x-v*(v@x)
    v=v-D0@L.solve(D0.T@v); v/=np.linalg.norm(v)
    Vt=torch.tensor(V); zt=torch.tensor(z)
    def f(theta,s):
        a=torch.tensor(s*v+proj(theta),requires_grad=True)
        U=tq(texp(a.reshape(4,N,N,N,N,3)),Vt); S=action(U,zt); S.backward()
        return float(S),proj(a.grad.numpy())
    prof=[]; theta=np.zeros(d)
    for t in np.linspace(0,tmax,nt):
        s=t/np.sqrt(q)
        r=minimize(lambda th:f(th,s),theta,jac=True,method='L-BFGS-B',options=dict(maxiter=3000,gtol=1e-9))
        theta=r.x; prof.append([float(t),float(r.fun)])
        print(json.dumps(dict(N=N,t=float(t),S=float(r.fun),free=float(t*t/2),it=int(r.nit))),flush=True)
    P=np.array(prof); d2=np.gradient(np.gradient(P[:,1],P[:,0]),P[:,0])
    tc=float(P[np.argmax(d2<0),0]) if (d2<0).any() else None
    res.append(dict(N=N,q=q,profile=prof,t_nonconvex=tc,S_max=float(P[:,1].max()),t_at_max=float(P[np.argmax(P[:,1]),0])))
    print(json.dumps(dict((k,res[-1][k]) for k in ('N','q','t_nonconvex','S_max','t_at_max'))),flush=True); json.dump(res,open(out,'w'))
