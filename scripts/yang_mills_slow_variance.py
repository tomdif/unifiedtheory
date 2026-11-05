"""Variance half of (S): is the slow flowed observable actually slow in Euclidean time? (numerics, not a proof).

(S) needs one flip-invariant g with E[(g(u1) - g(u0))^2] <= 2 (1 - e^{-C/n}) E[g^2] on the stationary chain of
consecutive time slices, i.e. 1 - rho1 <= C/n with rho1 the lag-one autocorrelation of g in Euclidean time.
The kinetic bound E[(dg)^2] <~ E|grad g|^2 / beta reduces this to q = beta_std Var g / E|grad g|^2 >~ n.
Same g as yang_mills_slow_force.py: sum_x cos(2 pi x3/n) * plaquette density after 3D Wilson flow to t = n^2/32,
evaluated on every time slice of each 4D twisted heatbath configuration.
Reports n (1 - rho1) (the end effect) and q / n (the reduction), plus the effective mass from the lag-1/lag-2 ratio.
Written before any run: n (1 - rho1) stays bounded (roughly flat, between 2 and 10) and q / n roughly flat.
n (1 - rho1) growing like n would mean g is not a slow observable at the generic scale.
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
    s=0.
    for m in range(3):
        for k in range(m+1,3):
            P=tq(tq(tq(U[m],torch.roll(U[k],-1,m)),torch.roll(U[m],-1,k)*CJ),U[k]*CJ)
            s=s+(1-(zt if (m,k)==(0,1) else 1.)*P[...,0])
    return s
def S3(U,zt): return plaq_density(U,zt).sum()
def flow(U,zt,t,eps=0.02,graph=True):
    for _ in range(int(round(t/eps))):
        w=torch.zeros(U.shape[:-1]+(3,),requires_grad=True)
        G,=torch.autograd.grad(S3(tq(texp(w),U),zt),w,create_graph=graph)
        U=tq(texp(-eps*G),U)
        if not graph: U=U.detach()
    return U

out=sys.argv[1]; ns=[int(x) for x in sys.argv[2].split(',')]; betas=[float(x) for x in sys.argv[3].split(',')]
ncfg=int(sys.argv[4]); res=[]
for N in ns:
    Lt=int(os.environ.get('TFAC','1'))*N; shp=(Lt,N,N,N)
    z=np.ones(shp); z[:,0,0,:]=-1; par=np.indices(shp).sum(0)%2
    zt=torch.tensor(z[0]); cosw=torch.tensor(np.cos(2*np.pi*np.indices((N,)*3)[2]/N))
    for bs in betas:
        rng=np.random.default_rng(int(100*bs)+N+7+int(os.environ.get('SEED','0')))
        U4=np.zeros((4,)+shp+(4,)); U4[...,0]=1
        if not os.environ.get('COLD'):   # flat twist-eating start (U=1 is not a vacuum of the twisted action)
            xx=np.indices(shp); U4[1][xx[1]==0]=[0,1,0,0]; U4[2][xx[2]==0]=[0,0,1,0]
        for _ in range(200): heat(U4,z,bs/2,rng,par); over(U4,z,par)
        rows=[]; G2=[]
        for c in range(ncfg):
            for _ in range(10): heat(U4,z,bs/2,rng,par); over(U4,z,par)
            gt=[]
            for t0 in range(Lt):
                U=torch.tensor(U4[1:,t0])
                if t0==0 and not os.environ.get('NOGRAD'):   # one gradient per configuration
                    w=torch.zeros(U.shape[:-1]+(3,),requires_grad=True)
                    g=(cosw*plaq_density(flow(tq(texp(w),U),zt,N*N/float(os.environ.get('FLOWC','32'))),zt)).sum()
                    gg,=torch.autograd.grad(g,w); G2.append(float((gg*gg).sum())); gt.append(float(g))
                else:
                    with torch.enable_grad(): gt.append(float((cosw*plaq_density(flow(U,zt,N*N/float(os.environ.get('FLOWC','32')),graph=False),zt)).sum()))
            rows.append(gt)
        A=np.array(rows); A=A-(0. if os.environ.get('ZEROMEAN') else A.mean())
        C=[float((A*np.roll(A,-k,1)).mean()) for k in range(Lt//2+1)]
        # error on 1 - rho1 by jackknife over configurations
        def onem(B): return 1-(B*np.roll(B,-1,1)).mean()/(B*B).mean()
        jk=np.array([onem(np.delete(A,i,0)) for i in range(len(A))]); om=onem(A)
        err=float(np.sqrt((len(A)-1)*((jk-jk.mean())**2).mean()))
        q=bs*C[0]/np.mean(G2) if G2 else float('nan')
        row=dict(N=N,beta_std=bs,var=C[0],one_minus_rho1=om,err=err,n_one_minus_rho1=N*om,q=q,q_over_n=q/N,
                 meff=float(-np.log(C[2]/C[1])) if C[1]>0 and C[2]>0 else None,C=C,cfgs=len(A),
                 flowc=float(os.environ.get('FLOWC','32')),g_raw=rows,Lt=Lt,Cn=[round(c/C[0],3) for c in C],
                 cfg_mean_over_sd=float(np.mean(rows)/np.sqrt(np.var(rows))))
        res.append(row); print(json.dumps({k:v for k,v in row.items() if k not in ('C','g_raw')}),flush=True); json.dump(res,open(out,'w'))
