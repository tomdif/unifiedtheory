"""Semiclassical rate of large-field blocks: least action of a non-convex side-2 fine block (numerics, not a proof).

yang_mills_block_convexity.py measured the probability p(beta) that a side-2 fine block is non-convex. Its local decay
rate grows with beta (6-8 at beta_std 2.25-3, up to ~12 at a near-zero threshold), so the strong-coupling fit
understates the large-beta rate. Semiclassically p ~ exp(-beta_std dS_min), where dS_min is the least action above the
vacuum of any configuration whose block fine Hessian has a non-positive eigenvalue. All (n/2)^4 blocks are then convex
with high probability iff beta_std > (4 / dS_min) log n, so dS_min > 4 / 0.371 = 10.8 would mean large-field blocks
vanish even on the asymptotic-freedom trajectory.
Method (gauge penalty K = 100 on the fine projections of all block sites' gauge generators): n = 4 twisted lattice, U = exp(a) V with V the flat twist-eater, block = side-2 block at the origin. The block
fine Hessian H_b(U) (zero-mean directions in frames transported by U, frames held fixed within each outer step) is the
torch.func Hessian of eps -> S(exp(T eps) U); lambda_min is differentiable. Minimize S(U) + kappa relu(lambda_min + d)^2
by Adam from several large-field starts, then report the least S with lambda_min <= 0. An upper bound on dS_min (local
optimization), not the minimum itself.
Written before any run: dS_min is between 3 and 10 (below the 10.8 needed), so large-field blocks persist at b*.
OBJ=max (env): instead of the total action, minimize the largest single-plaquette action tau*logsumexp(a_p/tau),
tau = 0.02, subject to lambda_min <= 0. This is the small-field threshold eps*: every configuration whose plaquettes
all have 1 - tr(P)/2 < eps* has a convex block (within the optimizer's reach), so eps* defines Balaban's small-field
region for this block geometry. Written before the OBJ=max run: eps* is between 0.3 and 1.0.
OBJ=lam (env, with EPS=e1,e2,...): the dual form, which converges faster. For each cap eps, minimize lambda_min
subject to every plaquette action <= eps (penalty kappa_e sum relu(a_p - eps)^2) and report Lambda(eps), the least
lambda_min reached with max a_p <= 1.02 eps. eps* is the zero of Lambda. Written before the OBJ=lam run: Lambda(eps)
crosses zero between eps = 0.3 and 1.0.
Usage: out n_starts n_steps
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
def plaq(U,zt):
    Pq=[]
    for m in range(4):
        for k in range(m+1,4):
            P=tq(tq(tq(U[m],torch.roll(U[k],-1,m)),torch.roll(U[m],-1,k)*CJ),U[k]*CJ)
            Pq.append(1-(zt if {m,k}=={1,2} else 1.)*P[...,0])
    return torch.stack(Pq).flatten()
OBJ=os.environ.get('OBJ','action'); TAU=0.02
def rotm(q):
    """Ad(q) as 3x3, for unit quaternions (..., 4)."""
    w,x,y,z=q.unbind(-1)
    return torch.stack([torch.stack([1-2*(y*y+z*z),2*(x*y-w*z),2*(x*z+w*y)],-1),
                        torch.stack([2*(x*y+w*z),1-2*(x*x+z*z),2*(y*z-w*x)],-1),
                        torch.stack([2*(x*z-w*y),2*(y*z+w*x),1-2*(x*x+y*y)],-1)],-2)

N=4; l=2; L=l**4
z=torch.tensor(twist(N)); V=torch.zeros((4,)+(N,)*4+(4,)); V[...,0]=1
xx=np.indices((N,)*4); V[1][torch.tensor(xx[1]==0)]=torch.tensor([0.,1,0,0]); V[2][torch.tensor(xx[2]==0)]=torch.tensor([0.,0,1,0])
sites=[tuple(s) for s in np.array(np.meshgrid(*[range(l)]*4,indexing='ij')).reshape(4,-1).T]   # block at origin
Hm=torch.tensor(np.linalg.svd(np.eye(L)-1./L)[0][:,:L-1])                                       # zero-mean basis of R^L
def frames(U):
    W={sites[0]:torch.tensor([1.,0,0,0])}
    for s in sites[1:]:
        for nu in range(4):
            if s[nu]>0:
                p=list(s); p[nu]-=1; p=tuple(p)
                if p in W: W[s]=tq(U[nu][p]*CJ,W[p]); break
    return torch.stack([rotm(W[s]) for s in sites])          # (L,3,3)
def block_hessian(U,R):
    def f(eps):       # eps: (4 directions, 3 colors, L-1) fine coordinates
        e=torch.einsum('mcj,ij->mic',eps,Hm)               # (4, L, 3) in transported frames
        e=torch.einsum('iab,mib->mia',R,e)                  # rotate to link coordinates
        Up=[U[m] for m in range(4)]
        for m in range(4):
            Um=U[m].clone()
            for i,s in enumerate(sites): Um[s]=tq(texp(e[m,i]),U[m][s])
            Up[m]=Um
        return action(torch.stack(Up),z)
    H=torch.func.hessian(f)(torch.zeros(4,3,L-1))
    k=4*3*(L-1); H=H.reshape(k,k)
    # gauge penalty: fine-space projections of the gauge generators of every block site (the gauge slice used
    # by the Monte Carlo test penalizes all sites' gauge directions); links leaving the block are dropped
    G=[]
    for xs in sites:
        i_x=sites.index(xs)
        for c in range(3):
            w=torch.zeros(3); w[c]=1.; dl=torch.zeros(4,L,3)
            for m in range(4):
                dl[m,i_x]=w
                p=list(xs); p[m]-=1; p=tuple(p)
                if p in sites: dl[m,sites.index(p)]=-rotm(U[m][p].detach())@w
            eta=torch.einsum('iba,mib->mia',R,dl)
            G.append(torch.einsum('mia,ij->maj',eta,Hm).reshape(-1))
    G=torch.stack(G,1); return H+Kpen*G@G.T

out=sys.argv[1]; nst=int(sys.argv[2]); nsteps=int(sys.argv[3]); kappa=200.; d=0.05; Kpen=100.; res=[]
S0=float(action(V,z)); print('vacuum action',S0,flush=True)
EPSL=[float(e) for e in os.environ.get('EPS','0').split(',')] if OBJ=='lam' else [None]
for EPS_now in EPSL:
 for st in range(nst):
     g=torch.Generator().manual_seed(st)
     a=0.05*torch.randn((4,)+(N,)*4+(3,),generator=g)
     # large-field seed inside the block: rotate one link per direction by an angle ~ 1.2-2
     for m in range(4): a[m][sites[st%L]]+=(1.2+0.1*st)*torch.nn.functional.normalize(torch.randn(3,generator=g),dim=0)
     a.requires_grad_(True); opt=torch.optim.Adam([a],lr=float(os.environ.get('LR','0.02'))); best=None
     for it in range(nsteps):
         U=tq(texp(a),V); R=frames(U.detach())
         H=block_hessian(U,R); lam=torch.linalg.eigvalsh((H+H.T)/2)[0]
         S=action(U,z)-S0
         if OBJ=='lam':
             pa=plaq(U,z); S=pa.max(); loss=lam+1e3*torch.relu(pa-EPS_now).pow(2).sum()
         elif OBJ=='max':
             pa=plaq(U,z); S=pa.max(); loss=TAU*torch.logsumexp(pa/TAU,0)+kappa*torch.relu(lam+d)**2
         else: loss=S+kappa*torch.relu(lam+d)**2
         opt.zero_grad(); loss.backward(); opt.step()
         if OBJ=='lam':
             if S.item()<=1.02*EPS_now and (best is None or lam.item()<best[1]): best=(S.item(),lam.item(),it)
         elif lam.item()<=0 and (best is None or S.item()<best[0]): best=(S.item(),lam.item(),it)
         if it%20==0: print(json.dumps(dict(start=st,it=it,dS=round(S.item(),4),lam_min=round(lam.item(),4))),flush=True)
     # diagnostic at the final configuration: how much of the lowest eigenvector is (approximately) gauge?
     with torch.no_grad():
         U=tq(texp(a),V); R=frames(U)
     H=block_hessian(U.detach(),R).detach(); w,Ev=torch.linalg.eigh((H+H.T)/2); v=Ev[:,0]
     Gs=[]
     for xs in sites:
         for c in range(3):
             wv=torch.zeros(3); wv[c]=1.; dl=torch.zeros(4,L,3); i_x=sites.index(xs)
             for m in range(4):
                 dl[m,i_x]=wv
                 p=list(xs); p[m]-=1; p=tuple(p)
                 if p in sites: dl[m,sites.index(p)]=-rotm(U[m][p].detach())@wv
             eta=torch.einsum('iba,mib->mia',R,dl); Gs.append(torch.einsum('mia,ij->maj',eta,Hm).reshape(-1))
     Q,_=torch.linalg.qr(torch.stack(Gs,1)); gauge_frac=float((Q.T@v).pow(2).sum())
     with torch.no_grad():
         Pq=[]
         for m in range(4):
             for k in range(m+1,4):
                 P=tq(tq(tq(U[m],torch.roll(U[k],-1,m)),torch.roll(U[m],-1,k)*CJ),U[k]*CJ)
                 Pq.append(1-(z if {m,k}=={1,2} else 1.)*P[...,0])
         pa=torch.stack(Pq).flatten(); top=torch.sort(pa,descending=True)[0][:8]
     row=dict(obj=OBJ,eps=EPS_now,start=st,best_dS_nonconvex=None if best is None else best[0],lam=None if best is None else best[1],it=None if best is None else best[2],
              final_lam=float(w[0]),gauge_fraction_of_lowest=gauge_frac,top_plaquette_actions=[round(float(x),3) for x in top])
     res.append(row); print(json.dumps(row),flush=True); json.dump(res,open(out,'w'))
