"""Step scaling of a blocked coupling on the twisted lattice (numerics, not a proof).

Twist n12 = 1 (one plaquette with sign -1), no zero modes. Averaged block map with center signs, as in TwistedBlockMap.
beta_eff(N, j) = c(N, j) / e(N, j), where e is the mean of 2 - 2 z Re P on the level-j lattice and c is its exact
twisted free value. At fixed coarse side N/2^j, doubling N at fixed bare beta doubles the physical size, so
beta_eff(N) - beta_eff(2N) should tend to about 0.129 (repo beta, one loop) as N grows.
Usage: out N beta_stds alphas n_therm n_meas. One heatbath plus three overrelaxation sweeps per update.
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

def twist(N):
    z=np.ones((N,N,N,N)); z[:,0,0,:]=-1
    return z
def zz(z,m,n):
    return z if {m,n}=={1,2} else 1.

def staple(U,z,m):
    tot=0.
    for n in range(4):
        if n==m: continue
        s=zz(z,m,n)
        up=qmul(qmul(S(U[n],m),qc(S(U[m],n))),qc(U[n]))
        bk=qmul(qmul(qc(S(U[n],m)),qc(U[m])),U[n])
        if s is not None and not np.isscalar(s):
            up=up*s[...,None]; bk=bk*s[...,None]
        tot=tot+up+S(bk,n,-1)
    return tot

def kp(k,rng):
    out=np.empty(k.shape); todo=np.ones(k.shape,bool)
    while todo.any():
        n=todo.sum(); ks=k[todo]
        r1,r2,r3,r4=rng.random(n),rng.random(n),rng.random(n),rng.random(n)
        lam2=-(np.log(1-r1)+np.cos(2*np.pi*r2)**2*np.log(1-r3))/(2*ks)
        ok=r4**2<=1-lam2
        idx=np.flatnonzero(todo); out[idx[ok]]=1-2*lam2[ok]; todo[idx[ok]]=False
    return out

def heat(U,z,beta,rng,par):
    for m in range(4):
        for p in (0,1):
            A=staple(U,z,m); nrm=np.linalg.norm(A,axis=-1); mask=(par==p)&(nrm>1e-12)
            a0=kp(2*beta*nrm[mask],rng)
            v=rng.normal(size=(a0.size,3)); v/=np.linalg.norm(v,axis=-1,keepdims=True)
            q=np.concatenate([a0[:,None],np.sqrt(np.clip(1-a0**2,0,None))[:,None]*v],-1)
            U[m][mask]=qmul(q,qc(A[mask]/nrm[mask][:,None]))

def over(U,z,par):
    for m in range(4):
        for p in (0,1):
            A=staple(U,z,m); nrm=np.linalg.norm(A,axis=-1); mask=(par==p)&(nrm>1e-12)
            Ah=qc(A[mask]/nrm[mask][:,None])
            U[m][mask]=qmul(qmul(Ah,qc(U[m][mask])),Ah)

def energy(U,z):
    tot=0
    for m in range(4):
        for n in range(m+1,4):
            P=qmul(qmul(qmul(U[m],S(U[n],m)),qc(S(U[m],n))),qc(U[n]))
            s=zz(z,m,n)
            tot+=(2-2*s*P[...,0]).mean()
    return tot/6

def block(U,z,alpha):
    out=[]
    for m in range(4):
        line=qmul(U[m],S(U[m],m)); tot=line.copy()
        for n in range(4):
            if n==m: continue
            s=zz(z,m,n)
            sg_up=s*S(s,m) if not np.isscalar(s) else 1.
            up=qmul(qmul(U[n],S(line,n)),qc(S(U[n],m,2)))
            if not np.isscalar(sg_up): up=up*sg_up[...,None]
            un=S(U[n],n,-1)
            dn=qmul(qmul(qc(un),S(line,n,-1)),S(un,m,2))
            if not np.isscalar(sg_up): dn=dn*S(sg_up,n,-1)[...,None]
            tot=tot+alpha*(up+dn)
        V=tot/np.linalg.norm(tot,axis=-1,keepdims=True)
        out.append(V[::2,::2,::2,::2])
    # the cell product of the four signs in the (1,2) plane, then subsample
    zc=(z*S(z,1)*S(z,2)*S(S(z,1),2))[::2,::2,::2,::2]
    return np.stack(out),zc

def free_kernel(k,a,alpha):
    ph=np.exp(1j*k*a); B=np.zeros(k.shape[:-1]+(4,4),complex)
    for m in range(4):
        line=1+ph[...,m]; B[...,m,m]+=line
        for n in range(4):
            if n==m: continue
            B[...,m,m]+=alpha*ph[...,n]*line
            B[...,m,n]+=alpha*(1-ph[...,m]**2)
            pb=np.conj(ph[...,n])
            B[...,m,m]+=alpha*pb*line
            B[...,m,n]+=alpha*pb*(ph[...,m]**2-1)
    return B/(1+6*alpha)

def free_c(N,alpha,jmax):
    tot=np.zeros(jmax+1)
    for e1,e2 in ((1,0),(0,1),(1,1)):
        g=2*np.pi*np.arange(N)/N
        k=np.stack(np.meshgrid(g,g+np.pi*e1/N,g+np.pi*e2/N,g,indexing='ij'),-1).reshape(-1,4)
        khat2=(4*np.sin(k/2)**2).sum(-1)
        B=np.tile(np.eye(4,dtype=complex),(k.shape[0],1,1))
        for j in range(jmax+1):
            a=2**j; D=np.exp(1j*k*a)-1; t=0.
            for m in range(4):
                for n in range(m+1,4):
                    f=D[...,m,None]*B[:,n,:]-D[...,n,None]*B[:,m,:]
                    t=t+(np.abs(f)**2).sum(-1)
            tot[j]+=float((t/6/(2*khat2)).sum()/N**4)
            if j<jmax: B=free_kernel(k,a,alpha)@B
    return tot.tolist()

if __name__=='__main__':
    out,N=sys.argv[1],int(sys.argv[2]); betas=[float(b) for b in sys.argv[3].split(',')]
    alphas=[float(a) for a in sys.argv[4].split(',')]; nt,nm=int(sys.argv[5]),int(sys.argv[6])
    jmax=int(np.log2(N))-2
    par=np.indices((N,)*4).sum(0)%2; z0=twist(N); res=[]
    free={a:free_c(N,a,jmax) for a in alphas}
    print('free',json.dumps(free),flush=True)
    def flat():
        U=np.zeros((4,N,N,N,N,4)); U[...,0]=1
        U[1][:,0,:,:]=np.array([0.,1,0,0]); U[2][:,:,0,:]=np.array([0.,0,1,0])
        return U
    for bstd in betas:
        rng=np.random.default_rng(int(bstd*100)+N); U=flat(); beta=bstd/2
        print('flat energy',energy(U,z0),flush=True)
        def upd():
            heat(U,z0,beta,rng,par)
            for _ in range(3): over(U,z0,par)
        for _ in range(nt): upd()
        rec={a:[] for a in alphas}
        for _ in range(nm):
            upd(); upd()
            for a in alphas:
                V,z=U,z0; es=[energy(V,z)]
                for _j in range(jmax):
                    V,z=block(V,z,a); es.append(energy(V,z))
                rec[a].append(es)
        for a in alphas:
            E=np.array(rec[a]); c=np.array(free[a]); n=E.shape[0]
            jk=np.array([c/np.delete(E,i,0).mean(0) for i in range(n)])
            be=c/E.mean(0); err=np.sqrt((n-1)*((jk-jk.mean(0))**2).sum(0)/n)
            r=dict(N=N,beta_std=bstd,alpha=a,c=c.tolist(),e=E.mean(0).tolist(),beta_eff=be.tolist(),err=err.tolist(),n=n)
            res.append(r); print(json.dumps(r),flush=True)
    json.dump(res,open(out,'w'),indent=1)
