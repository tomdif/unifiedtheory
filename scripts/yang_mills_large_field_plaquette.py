"""Cost of a large-field plaquette: least action with one plaquette at a_p >= eps (numerics, not a proof).

The small-field threshold for side-2 block convexity is eps* ~ 0.25-0.30 (README, "Small-field threshold eps*"). A
Balaban large-field region starts wherever some plaquette has a_p = 1 - tr(P)/2 >= eps*. Two quantities:
(1) dS_1(eps): the least action above the twisted vacuum of a configuration with one chosen plaquette at a_p >= eps
    (n = 4 and 6, Adam on Lie-algebra coordinates, penalty on the constraint). To quadratic order this is
    eps / G, where G = <e_p, P_exact e_p> = 1/2 - O(1/V) is the overlap of a plaquette with exact 2-forms, so dS_1 = 2 eps.
(2) The Monte Carlo frequency f(beta) of plaquettes with a_p >= eps (heat bath, weight exp(-beta_std sum a_p)), and
    its local decay rate -d log f / d beta_std, to compare with dS_1.
Written before any run: dS_1(0.27) is between 0.45 and 0.6 (Gaussian value 0.54, lowered slightly by the nonlinearity)
and the Monte Carlo rate approaches it from below at large beta. Then at the asymptotic-freedom slope
(beta_std = 0.371 log n) the density of large-field plaquettes falls only like n^{-0.2}: they are everywhere, and
convexity cannot be proved pointwise on a small-field region; the argument must use averaged (or coherent) quantities.
Usage: out
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
    th=torch.sqrt((a*a).sum(-1,keepdim=True)+1e-30)
    return torch.cat([torch.cos(th),torch.sin(th)/th*a],-1)
def plaq(U,zt):
    Pq=[]
    for m in range(4):
        for k in range(m+1,4):
            P=tq(tq(tq(U[m],torch.roll(U[k],-1,m)),torch.roll(U[m],-1,k)*CJ),U[k]*CJ)
            Pq.append(1-(zt if {m,k}=={1,2} else 1.)*P[...,0])
    return torch.stack(Pq).flatten()

out=sys.argv[1]; res=[]

def vacuum(N):
    V=torch.zeros((4,)+(N,)*4+(4,)); V[...,0]=1; xx=np.indices((N,)*4)
    V[1][torch.tensor(xx[1]==0)]=torch.tensor([0.,1,0,0]); V[2][torch.tensor(xx[2]==0)]=torch.tensor([0.,0,1,0])
    return V

for N in (4,6):
    z=torch.tensor(twist(N)); V=vacuum(N); S0=float(plaq(V,z).sum())
    for eps in (0.1,0.2,0.27,0.35,0.5):
        g=torch.Generator().manual_seed(0)
        a=(0.01*torch.randn((4,)+(N,)*4+(3,),generator=g)).requires_grad_(True); opt=torch.optim.Adam([a],lr=0.01)
        # plaquette index 0 of the (0,1) plane at x = (2,2,2,2): away from the twist sheets
        for it in range(3000):
            pa=plaq(tq(texp(a),V),z); pl=pa.reshape(6,*(N,)*4)
            p0=pl[0,2,2,2,2]; loss=pa.sum()-S0+1e4*torch.relu(eps-p0)**2
            opt.zero_grad(); loss.backward(); opt.step()
            if it==1500:
                for gq in opt.param_groups: gq['lr']=0.003
        with torch.no_grad():
            pa=plaq(tq(texp(a),V),z); dS=float(pa.sum()-S0); p0=float(pa.reshape(6,*(N,)*4)[0,2,2,2,2])
            top=torch.sort(pa,descending=True)[0][:6]
        row=dict(kind='min',N=N,eps=eps,a_p0=p0,dS1=dS,ratio=dS/p0,top=[round(float(x),4) for x in top])
        res.append(row); print(json.dumps(row),flush=True); json.dump(res,open(out,'w'))

# Monte Carlo frequency of large plaquettes
N=6; z=twist(N); par=np.indices((N,)*4).sum(0)%2; rng=np.random.default_rng(5)
from yang_mills_twisted_step_scaling import qmul, qc
def plaq_np(U):
    out=[]
    for m in range(4):
        for k in range(m+1,4):
            P=qmul(qmul(qmul(U[m],np.roll(U[k],-1,m)),qc(np.roll(U[m],-1,k))),qc(U[k]))
            out.append(1-(z if {m,k}=={1,2} else 1.)*P[...,0])
    return np.stack(out).ravel()
U=vacuum(N).numpy().copy()
for b in (3.,4.,5.,6.,8.,10.,12.):
    for _ in range(200): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
    acc={e:0 for e in (0.1,0.2,0.27,0.35,0.5)}; tot=0; mean=0.
    for c in range(200):
        for _ in range(5): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
        pa=plaq_np(U); tot+=pa.size; mean+=pa.sum()
        for e in acc: acc[e]+=int((pa>=e).sum())
    row=dict(kind='mc',N=N,bstd=b,mean_a=mean/tot,freq={str(e):acc[e]/tot for e in acc})
    res.append(row); print(json.dumps(row),flush=True); json.dump(res,open(out,'w'))
