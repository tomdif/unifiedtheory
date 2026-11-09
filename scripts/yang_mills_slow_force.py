"""Slow-force test for the kinetic half of (S) (numerics, not a proof).

(K2) needs E[F^2] <= C E|grad g|^2 / beta_std for a slow, flip-invariant, gauge-invariant slice observable g, with
F = <grad g, grad S3> and S3 = sum over the spatial plaquettes of one time slice of (1 - z P0). Any C independent of n
is enough. Cauchy-Schwarz alone gives r ~ n; a free field gives r ~ omega^2 ~ 1/n^2.
g = sum_x cos(2 pi x3/n) s(x), where s is the plaquette density after 3D Wilson flow to t = n^2/32 (differentiable).
Gradients are taken along left perturbations exp(eps) U, on configurations from the 4D twisted heatbath (time axis 0,
twist in the spatial (1,2) planes). Reports r = beta_std E[F^2] / E|grad g|^2.
Written before any run: r <= 1 at every n and beta_std, and it decreases with n (r n^2 roughly flat). Growth of r
with n would kill (K2) at the generic scale.
Usage: out ns betas ncfg
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, torch
from yang_mills_twisted_step_scaling import twist, heat, over
torch.set_default_dtype(torch.float64); torch.set_num_threads(1)

def tq(a,b):
    w1,x1,y1,z1=a.unbind(-1); w2,x2,y2,z2=b.unbind(-1)
    return torch.stack([w1*w2-x1*x2-y1*y2-z1*z2,w1*x2+x1*w2+y1*z2-z1*y2,w1*y2-x1*z2+y1*w2+z1*x2,w1*z2+x1*y2-y1*x2+z1*w2],-1)
CJ=torch.tensor([1.,-1,-1,-1])
def texp(a):
    th=torch.sqrt((a*a).sum(-1,keepdim=True)+1e-300)
    return torch.cat([torch.cos(th),torch.where(th>1e-8,torch.sin(th)/th,1-th*th/6)*a],-1)
def plaq_density(U,zt):
    """U: (3,n,n,n,4) spatial links, axes = spatial directions 1,2,3; zt twist on the (1,2) planes (axes 0,1 here)."""
    s=0.
    for m in range(3):
        for k in range(m+1,3):
            P=tq(tq(tq(U[m],torch.roll(U[k],-1,m)),torch.roll(U[m],-1,k)*CJ),U[k]*CJ)
            s=s+(1-(zt if (m,k)==(0,1) else 1.)*P[...,0])
    return s
def S3(U,zt): return plaq_density(U,zt).sum()
def flow(U,zt,t,eps=0.02):
    for _ in range(int(round(t/eps))):
        w=torch.zeros(U.shape[:-1]+(3,),requires_grad=True)
        G,=torch.autograd.grad(S3(tq(texp(w),U),zt),w,create_graph=True)
        U=tq(texp(-eps*G),U)
    return U

out=sys.argv[1]; ns=[int(x) for x in sys.argv[2].split(',')]; betas=[float(x) for x in sys.argv[3].split(',')]
ncfg=int(sys.argv[4]); res=[]
for N in ns:
    z=twist(N); par=np.indices((N,)*4).sum(0)%2
    zt=torch.tensor(z[0])   # twist of the spatial (1,2) planes in slice t = 0: z[:,0,0,:] -> slice shape (N,N,N)
    cosw=torch.tensor(np.cos(2*np.pi*np.indices((N,)*3)[2]/N))
    for bs in betas:
        rng=np.random.default_rng(int(100*bs)+N+int(os.environ.get('SEED','0')))
        U4=np.zeros((4,)+(N,)*4+(4,)); U4[...,0]=1
        for _ in range(200): heat(U4,z,bs/2,rng,par); over(U4,z,par)
        F2=[]; G2=[]
        for c in range(ncfg):
            for _ in range(10): heat(U4,z,bs/2,rng,par); over(U4,z,par)
            for t0 in range(0,N,2):   # several time slices per configuration
                U=torch.tensor(U4[1:,t0])
                w=torch.zeros(U.shape[:-1]+(3,),requires_grad=True)
                Uw=tq(texp(w),U)
                g=(cosw*plaq_density(flow(Uw,zt,N*N/32.),zt)).sum()
                gg,=torch.autograd.grad(g,w)
                w2=torch.zeros_like(w,requires_grad=True)
                gs,=torch.autograd.grad(S3(tq(texp(w2),U),zt),w2)
                F2.append(float((gg*gs).sum())**2); G2.append(float((gg*gg).sum()))
        F2=np.array(F2); G2=np.array(G2); r=bs*F2.mean()/G2.mean()
        row=dict(N=N,beta_std=bs,r=r,r_err=bs*F2.std()/np.sqrt(len(F2))/G2.mean(),r_n2=r*N*N,samples=len(F2),
                 r_median_ratio=bs*float(np.median(F2/G2)),F2=F2.tolist(),G2=G2.tolist())
        res.append(row); print(json.dumps({k:v for k,v in row.items() if k not in ('F2','G2')}),flush=True); json.dump(res,open(out,'w'))
