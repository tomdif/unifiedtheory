"""Does a block-spin map keep plaquette defects stable? (numerics, not a proof)

SU(2) Wilson heatbath, untwisted (the twist is one plaquette in N^4 and does not affect local averages).
Block maps by factor 2: path product (decimation, alpha = 0), or the projection of the path product plus alpha
times the six length-4 staples. Reports e_k = <2 - 2 Re P> at blocking level k, and the ratio e_{k+1}/e_k.
An RG-stable map should have a ratio near 1 at weak coupling, since the running coupling barely changes.
Weight is exp(-beta S), S = sum (2 - 2 Re P), so beta_std = 2 beta.
"""
import os
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='2'
import sys, json, numpy as np

def qmul(a,b):
    w1,x1,y1,z1=a[...,0],a[...,1],a[...,2],a[...,3]; w2,x2,y2,z2=b[...,0],b[...,1],b[...,2],b[...,3]
    return np.stack([w1*w2-x1*x2-y1*y2-z1*z2,w1*x2+x1*w2+y1*z2-z1*y2,w1*y2-x1*z2+y1*w2+z1*x2,w1*z2+x1*y2-y1*x2+z1*w2],-1)
CONJ=np.array([1.,-1,-1,-1])
def qc(a): return a*CONJ
def S(f,m,k=1): return np.roll(f,-k,axis=m)

def staple(U,m):
    tot=0.
    for n in range(4):
        if n==m: continue
        up=qmul(qmul(S(U[n],m),qc(S(U[m],n))),qc(U[n]))
        bk=S(qmul(qmul(qc(S(U[n],m)),qc(U[m])),U[n]),n,-1)
        tot=tot+up+bk
    return tot

def kp(k,rng):
    """a0 with density exp(k a0) sqrt(1-a0^2), Kennedy-Pendleton, vectorized"""
    out=np.empty(k.shape); todo=np.ones(k.shape,bool)
    while todo.any():
        n=todo.sum(); ks=k[todo]
        r1,r2,r3,r4=rng.random(n),rng.random(n),rng.random(n),rng.random(n)
        lam2=-(np.log(1-r1)+np.cos(2*np.pi*r2)**2*np.log(1-r3))/(2*ks)
        ok=r4**2<=1-lam2
        idx=np.flatnonzero(todo)
        out[idx[ok]]=1-2*lam2[ok]
        todo[idx[ok]]=False
    return out

def heat(U,beta,rng,par):
    for m in range(4):
        for p in (0,1):
            A=staple(U,m)
            nrm=np.linalg.norm(A,axis=-1)
            mask=(par==p)&(nrm>1e-12)
            a0=kp(2*beta*nrm[mask],rng)
            v=rng.normal(size=(a0.size,3)); v/=np.linalg.norm(v,axis=-1,keepdims=True)
            q=np.concatenate([a0[:,None],np.sqrt(np.clip(1-a0**2,0,None))[:,None]*v],-1)
            Ah=(A[mask]/nrm[mask][:,None])
            U[m][mask]=qmul(q,qc(Ah))
    return U

def energy(U):
    d=U.shape[1]; tot=0;c=0
    for m in range(4):
        for n in range(m+1,4):
            P=qmul(qmul(qmul(U[m],S(U[n],m)),qc(S(U[m],n))),qc(U[n]))
            tot+=(2-2*P[...,0]).mean();c+=1
    return tot/c

def block(U,alpha):
    out=[]
    for m in range(4):
        V=qmul(U[m],S(U[m],m))
        if alpha>0:
            tot=V.copy()
            line=V
            for n in range(4):
                if n==m: continue
                tot=tot+alpha*qmul(qmul(U[n],S(line,n)),qc(S(U[n],m,2)))
                un=S(U[n],n,-1)
                tot=tot+alpha*qmul(qmul(qc(un),S(line,n,-1)),S(un,m,2))
            V=tot/np.linalg.norm(tot,axis=-1,keepdims=True)
        out.append(V[::2,::2,::2,::2])
    return np.stack(out)

N=int(sys.argv[2]); res=[]
grid=np.indices((N,)*4).sum(0)%2
alphas=tuple(float(a) for a in sys.argv[6].split(',')) if len(sys.argv)>6 else (0.,0.1,0.25,0.5,1.0)
betas=tuple(float(b) for b in sys.argv[5].split(',')) if len(sys.argv)>5 else (2.5,4.,8.,16.,64.)
for bstd in betas:
    rng=np.random.default_rng(int(bstd*10))
    U=np.zeros((4,N,N,N,N,4)); U[...,0]=1
    beta=bstd/2
    for _ in range(int(sys.argv[3])): heat(U,beta,rng,grid)
    rec={a:[[] for _ in range(4)] for a in alphas}
    for _ in range(int(sys.argv[4])):
        for _ in range(5): heat(U,beta,rng,grid)
        for a in alphas:
            V=U; rec[a][0].append(energy(V)); lv=1
            while V.shape[1]>=4 and lv<4:
                V=block(V,a); rec[a][lv].append(energy(V)); lv+=1
    for a in alphas:
        es=[float(np.mean(x)) for x in rec[a] if x]
        r=dict(beta_std=bstd,N=N,alpha=a,e=es,ratio=[es[i+1]/es[i] for i in range(len(es)-1)],free_e_estimate=None)
        res.append(r); print(json.dumps(r),flush=True)
json.dump(res,open(sys.argv[1],'w'),indent=1)
