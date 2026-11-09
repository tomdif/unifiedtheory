"""Class-resolved sign of the loop-equation cross terms on the twisted heatbath (numerics, not a proof).

For a link U_m(x), reports E<Im c_p, Im c_q> split by the pair's type:
  opp_time   same plane, opposite plaquette, n in {0,3}: reflection through x fixes the twist
  opp_twist  same plane, opposite plaquette, n in {1,2}: no reflection positivity available
  other      different planes, split by whether either plane is (1,2)
Errors come from blocking the sweeps into 50 bins.
"""
import os, sys
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0,os.path.dirname(__file__))
import numpy as np, json
from yang_mills_twisted_step_scaling import qmul,qc,S as sh,twist,zz,heat,over

def flat(N):
    U=np.zeros((4,N,N,N,N,4)); U[...,0]=1
    U[1][:,0,:,:]=np.array([0.,1,0,0]); U[2][:,:,0,:]=np.array([0.,0,1,0])
    return U
def cs(U,z,m):
    out={}
    for n in range(4):
        if n==m: continue
        s=zz(z,m,n)
        up=qmul(qmul(sh(U[n],m),qc(sh(U[m],n))),qc(U[n]))
        bk=sh(qmul(qmul(qc(sh(U[n],m)),qc(U[m])),U[n]),n,-1)
        sb=sh(s,n,-1) if not np.isscalar(s) else 1.
        cu=qmul(U[m],up); cb=qmul(U[m],bk)
        if not np.isscalar(s):
            cu=cu*s[...,None]; cb=cb*sb[...,None]
        out[(n,1)]=cu; out[(n,-1)]=cb
    return out
def cls(m,k1,k2):
    if k1[0]==k2[0]: return 'opp_time' if k1[0] in (0,3) else 'opp_twist'
    return 'other_12' if ({m,k1[0]}=={1,2} or {m,k2[0]}=={1,2}) else 'other_free'

out,N,sweeps=sys.argv[1],int(sys.argv[2]),int(sys.argv[3])
res=[]
for bstd in [float(b) for b in sys.argv[4].split(',')]:
    beta=bstd/2; rng=np.random.default_rng(int(bstd*100)+7); z=twist(N); par=np.indices((N,)*4).sum(0)%2
    U=flat(N)
    for _ in range(200):
        heat(U,z,beta,rng,par); over(U,z,par)
    names=('opp_time','opp_twist','other_12','other_free'); rows=[]; pairs={}
    for _ in range(sweeps):
        heat(U,z,beta,rng,par); over(U,z,par)
        t={k:[0.,0] for k in names}
        for m in range(4):
            q=cs(U,z,m); ks=sorted(q)
            for i,k1 in enumerate(ks):
                for k2 in ks[i+1:]:
                    v=float((q[k1][...,1:]*q[k2][...,1:]).sum(-1).mean())
                    c=cls(m,k1,k2); t[c][0]+=v; t[c][1]+=1
                    pairs.setdefault((m,)+k1+k2,[]).append(v)
        rows.append([t[k][0]/t[k][1] for k in names])
    bins=np.array_split(np.array(rows),50); b=np.array([x.mean(0) for x in bins])
    r=dict(N=N,beta_std=bstd,sweeps=sweeps)
    for i,k in enumerate(names): r[k]=[float(b[:,i].mean()),float(b[:,i].std(ddof=1)/np.sqrt(50))]
    pz=[]
    for k,v in pairs.items():
        bb=np.array([x.mean() for x in np.array_split(np.array(v),50)])
        pz.append((float(bb.mean()/(bb.std(ddof=1)/np.sqrt(50))),float(bb.mean()),k))
    pz.sort(); r['n_pairs']=len(pz); r['n_negative']=sum(p[1]<0 for p in pz); r['worst_z']=pz[0][0]; r['worst_mean']=pz[0][1]; r['worst_pair']=list(pz[0][2])
    print(json.dumps(r),flush=True); res.append(r)
    json.dump(res,open(out,'w'),indent=1)
