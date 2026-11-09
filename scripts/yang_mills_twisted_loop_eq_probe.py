"""Single-plaquette loop equation on the twisted heatbath (numerics, not a proof).

At a link U_m(x), all plaquettes containing it are c_q = z U_m(x) s_q, with the flow exp(tY)U acting on the left.
Integration by parts with f = Re c_p, summed over three colours, gives
  2 beta sum_q E<Im c_p, Im c_q> = 3 E[Re c_p].
Reports the q = p term, the opposite plaquette in the same plane, and the four in other planes, to test the sign of
the cross terms. If all were nonnegative then E|Im c_p|^2 <= 3/(2 beta).
"""
import os, sys
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='2'
sys.path.insert(0,os.path.dirname(__file__))
import numpy as np, json
from yang_mills_twisted_step_scaling import qmul,qc,S as sh,twist,zz,heat,over

def flat(N):
    U=np.zeros((4,N,N,N,N,4)); U[...,0]=1
    U[1][:,0,:,:]=np.array([0.,1,0,0]); U[2][:,:,0,:]=np.array([0.,0,1,0])
    return U
def cs(U,z,m):
    """returns dict (n,sign) -> field of c_q at each x"""
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

res=[]; N=int(sys.argv[2])
for bstd in (1.,2.,2.5,4.,8.,16.):
    beta=bstd/2; rng=np.random.default_rng(int(bstd*10)); z=twist(N); par=np.indices((N,)*4).sum(0)%2
    U=flat(N)
    for _ in range(60):
        heat(U,z,beta,rng,par)
        for _ in range(2): over(U,z,par)
    rows=[]; pairs={}
    for _ in range(int(sys.argv[3])):
        heat(U,z,beta,rng,par); over(U,z,par)
        own=opp=oth=rec=0.; c=0
        for m in range(4):
            q=cs(U,z,m)
            for (n,sg),cp in q.items():
                own+=(cp[...,1:]**2).sum(-1).mean()
                for k2,c2 in q.items():
                    if k2!=(n,sg):
                        pairs.setdefault((m,n,sg,k2[0],k2[1]),[]).append(float((cp[...,1:]*c2[...,1:]).sum(-1).mean()))
                rec+=cp[...,0].mean()
                opp+=(cp[...,1:]*q[(n,-sg)][...,1:]).sum(-1).mean()
                oth+=sum((cp[...,1:]*q[k][...,1:]).sum(-1).mean() for k in q if k[0]!=n)/4
                c+=1
        rows.append([own/c,opp/c,oth/c,rec/c])
    a=np.array(rows); mean=a.mean(0); err=a.std(0,ddof=1)/np.sqrt(len(a))
    lhs=2*beta*(mean[0]+mean[1]+4*mean[2]); rhs=3*mean[3]
    pm={k:(float(np.mean(v)),float(np.std(v,ddof=1)/np.sqrt(len(v)))) for k,v in pairs.items()}
    worst=min(pm.items(),key=lambda kv:kv[1][0]/max(kv[1][1],1e-12))
    print('pairs',len(pm),'negative',sum(v[0]<0 for v in pm.values()),'worst',worst[0],worst[1],'most negative',min(v[0] for v in pm.values()),flush=True)
    r=dict(N=N,beta_std=bstd,n_pairs=len(pm),n_negative=sum(v[0]<0 for v in pm.values()),worst_pair=list(worst[0]),worst_mean=worst[1][0],worst_err=worst[1][1],own=mean[0],opp=mean[1],other=mean[2],re=mean[3],err=err.tolist(),lhs=lhs,rhs=rhs,own_times_2beta=2*beta*mean[0],local_bound_3_over_2beta=3/(2*beta))
    res.append(r); print(json.dumps(r),flush=True)
json.dump(res,open(sys.argv[1],'w'),indent=1)
