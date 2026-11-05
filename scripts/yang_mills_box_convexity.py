"""Is a side-2 block's Wilson action convex on a link box {|x_l| <= eps} in a FIXED linear chart? (numerics, not a proof)

TwistedPrekopaDomain proves the convex RG step on a convex small-field domain D, with joint convexity of the action on
D in fixed linear coordinates. The natural convex D is a box in Lie-algebra link coordinates, U_l = exp(x_l) V_l
around the twist-eater V, |x_l| <= eps for every link. Fine variables: the 17 non-tree internal links of the side-2
block at the origin (exact axial gauge on a maximal tree inside the block, tree links fixed at V, Jacobian 1).
For each eps, minimize lambda_min of the 51x51 fixed-chart Hessian of S(x) in the fine variables over all lattice
configurations in the box (Adam; x_l = eps tanh|u| u/|u|), from several random starts. Report Lambda(eps), the least
lambda_min found (an upper bound on the true minimum), for n = 4 and n = 6.
The Haar density in exponential coordinates, (sin|x|/|x|)^2, is left out. Its -log is convex, so leaving it out is
conservative.
Written before any run: Lambda(eps) crosses zero between eps = 0.2 and 0.5. Since the block is local, the crossing
is the same at n = 4 and n = 6 to within 0.05.
Usage: out ns eps_list n_starts n_steps
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, torch
from yang_mills_twisted_step_scaling import twist
torch.set_default_dtype(torch.float64); torch.set_num_threads(1)
def tq(a,b):
    w1,x1,y1,z1=a.unbind(-1); w2,x2,y2,z2=b.unbind(-1)
    return torch.stack([w1*w2-x1*x2-y1*y2-z1*z2,w1*x2+x1*w2+y1*z2-z1*y2,w1*y2-x1*z2+y1*w2+z1*x2,w1*z2+x1*y2-y1*x2+z1*w2],-1)
CJ=torch.tensor([1.,-1,-1,-1])
def texp(a):
    th=torch.sqrt((a*a).sum(-1,keepdim=True)+1e-30)
    return torch.cat([torch.cos(th),torch.sin(th)/th*a],-1)
def action(U,zt):
    S=0.
    for m in range(4):
        for k in range(m+1,4):
            P=tq(tq(tq(U[m],torch.roll(U[k],-1,m)),torch.roll(U[m],-1,k)*CJ),U[k]*CJ)
            S=S+(1-(zt if {m,k}=={1,2} else 1.)*P[...,0]).sum()
    return S

out=sys.argv[1]; ns=[int(v) for v in sys.argv[2].split(',')]; epsl=[float(v) for v in sys.argv[3].split(',')]
nst=int(sys.argv[4]); nsteps=int(sys.argv[5]); res=[]
for N in ns:
    z=torch.tensor(twist(N)); V=torch.zeros((4,)+(N,)*4+(4,)); V[...,0]=1
    xx=np.indices((N,)*4); V[1][torch.tensor(xx[1]==0)]=torch.tensor([0.,1,0,0]); V[2][torch.tensor(xx[2]==0)]=torch.tensor([0.,0,1,0])
    sites=[tuple(s) for s in np.array(np.meshgrid(*[range(2)]*4,indexing='ij')).reshape(4,-1).T]
    tree=set()
    for s in sites[1:]:
        nu=next(k for k in range(4) if s[k]>0); p=list(s); p[nu]-=1; tree.add((nu,tuple(p)))
    internal=[(m,s) for s in sites for m in range(4) if s[m]==0]
    fine=[l for l in internal if l not in tree]                       # 17 links
    mask=torch.ones((4,)+(N,)*4+(1,))
    for (m,s) in tree: mask[(m,)+s]=0.
    idx=[(m,)+s for (m,s) in fine]
    def S_of(x):
        return action(tq(texp(x),V),z)
    def lam_min(x):
        def f(e):
            xe=x.clone()
            for i,ix in enumerate(idx): xe[ix]=x[ix]+e[i]
            return S_of(xe)
        H=torch.func.hessian(f)(torch.zeros(len(fine),3)).reshape(3*len(fine),3*len(fine))
        return torch.linalg.eigvalsh((H+H.T)/2)[0]
    x0=torch.zeros((4,)+(N,)*4+(3,)); lam0=float(lam_min(x0)); print(json.dumps(dict(N=N,lam_vacuum=lam0)),flush=True)
    for eps in epsl:
        best=None
        for st in range(nst):
            g=torch.Generator().manual_seed(100*st+N)
            u=(1.5*torch.randn((4,)+(N,)*4+(3,),generator=g)).requires_grad_(True)
            opt=torch.optim.Adam([u],lr=0.05)
            for it in range(nsteps):
                r=torch.sqrt((u*u).sum(-1,keepdim=True)+1e-30); x=eps*torch.tanh(r)/r*u*mask
                lam=lam_min(x); opt.zero_grad(); lam.backward(); opt.step()
                if best is None or lam.item()<best[0]:
                    best=(lam.item(),float(torch.sqrt((x*x).sum(-1)).max()),st,it)
            print(json.dumps(dict(N=N,eps=eps,start=st,lam_final=round(lam.item(),4),best=round(best[0],4))),flush=True)
        row=dict(N=N,eps=eps,lam_vacuum=lam0,Lambda=best[0],max_link=best[1],start=best[2],it=best[3],starts=nst,steps=nsteps)
        res.append(row); print(json.dumps(row),flush=True); json.dump(res,open(out,'w'))
