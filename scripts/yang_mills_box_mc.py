"""Do typical blocks lie in the link box {|x_l| <= eps}? Axial-gauge link angles in Monte Carlo (numerics, not a proof).

Companion to yang_mills_box_convexity.py. That script finds eps_box, the box size below which a side-2 block's action
is convex in the fine variables (fixed chart, axial gauge on a tree inside the block). Here, for each side-2 block of
the Monte Carlo lattice (blocks based at even sites), the block is put in the same axial gauge: tree links set to 1
by the gauge transformation W_s = product of tree links from the root. Then the angle theta_l = arccos(w) of each of the
17 non-tree internal links is recorded. Blocks containing a twisted plaquette are skipped (their reference is the
twist-eater, not 1). Reported per beta_std:
  quantiles of theta_l;
  quantiles of the per-block maximum;
  the fraction of blocks with max theta <= eps for each eps.
Written before any run: the median link angle scales like c/sqrt(beta_std) with c ~ 1.5-2.5, since the non-tree
links are holonomies of loops enclosing 1-3 plaquettes. So for blocks to sit in a box of size ~0.3-0.5, beta_std must
be well above 10.
Usage: out N beta_stds n_cfg
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np
from yang_mills_twisted_step_scaling import twist, heat, over, qmul, qc

out=sys.argv[1]; N=int(sys.argv[2]); bs=[float(v) for v in sys.argv[3].split(',')]; ncfg=int(sys.argv[4])
sites=[tuple(s) for s in np.array(np.meshgrid(*[range(2)]*4,indexing='ij')).reshape(4,-1).T]
parent={}
for s in sites[1:]:
    nu=next(k for k in range(4) if s[k]>0); p=list(s); p[nu]-=1; parent[s]=(nu,tuple(p))
tree={(nu,p) for (nu,p) in parent.values()}
fine=[(m,s) for s in sites for m in range(4) if s[m]==0 and (m,s) not in tree]
assert len(fine)==17
def sl(F,s): return F[s[0]::2, s[1]::2, s[2]::2, s[3]::2]
nb=N//2; bx=np.indices((nb,)*4)*2
twisted_block=(bx[1]==0)&(bx[2]==0)                       # contains the (1,2) plaquette at x1=x2=0
EPS=[0.1,0.2,0.3,0.4,0.5,0.7,1.0]
z=twist(N); par=np.indices((N,)*4).sum(0)%2; rng=np.random.default_rng(11)
U=np.zeros((4,)+(N,)*4+(4,)); U[...,0]=1; xx=np.indices((N,)*4)
U[1][xx[1]==0]=[0,1,0,0]; U[2][xx[2]==0]=[0,0,1,0]
res=[]
for b in bs:
    for _ in range(150): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
    th_all=[]; th_max=[]
    for c in range(ncfg):
        for _ in range(10): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
        W={sites[0]:np.broadcast_to(np.array([1.,0,0,0]),(nb,)*4+(4,)).copy()}
        for s in sites[1:]:
            nu,p=parent[s]; W[s]=qmul(W[p],sl(U[nu],p))       # so W_p U W_s^-1 = 1 on tree links
        ths=[]
        for (m,p) in fine:
            q=list(p); q[m]+=1; q=tuple(q)
            Ut=qmul(qmul(W[p],sl(U[m],p)),qc(W[q]))
            ths.append(np.arccos(np.clip(Ut[...,0],-1,1))[~twisted_block])
        ths=np.stack(ths)                                      # (17, blocks)
        th_all.append(ths.ravel()); th_max.append(ths.max(0))
    th_all=np.concatenate(th_all); th_max=np.concatenate(th_max)
    row=dict(N=N,bstd=b,cfgs=ncfg,link_q=[round(float(v),4) for v in np.quantile(th_all,[0.1,0.5,0.9,0.99])],
             blockmax_q=[round(float(v),4) for v in np.quantile(th_max,[0.1,0.5,0.9,0.99])],
             frac_in_box={str(e):float((th_max<=e).mean()) for e in EPS},
             link_frac_le={str(e):float((th_all<=e).mean()) for e in EPS})
    res.append(row); print(json.dumps(row),flush=True); json.dump(res,open(out,'w'))
