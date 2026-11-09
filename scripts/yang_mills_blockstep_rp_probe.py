"""Does reflection positivity survive one block step? And does the reflection-compatible map roughen? (numerics, not a proof)

Maps: `iso` is the map of TwistedBlockMap (six staples on every link). `aniso` drops the staples of a spatial link that
cross time slices, so spatial links stay on their slice. Modes:

free out N       exact free ratios c_{j+1}/c_j of the blocked defect, spatial and temporal planes, both maps.
hankel out L     exact free one-gluon correlator of the blocked winding trW1 (k1 = 0, k2 = pi/L, k3 = 0), coarse times 0, 1, 2.
                 RP requires C0*C2 >= C1^2. Also gauge-invariant untwisted F12 at each spatial momentum.
mc out L T bstd maps ntherm nmeas seed  the same ratio on a heatbath of the actual twisted law, several maps on one chain.
                                        maps is e.g. iso:0.15,aniso:0.15,fine:0. Records seed, ntherm, sweeps per measurement,
                                        jackknife errors by bin count, integrated autocorrelation times and half-chain ratios.
                                        T = L is the hypercubic lattice of the Lean theorems; T > L is not.
rank out N alpha nconf                  rank and smallest singular value of the differential of the block map.
two out                                 free ratios for reflection-compatible weights with separate spatial and time values.
interp out n nconf                      checks the interpolation of TwistedBlockStep on random coarse fields: its lines, its defects.
"""
import os
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='2'
import sys, json, numpy as np

def weights(kind, alpha):
    a=np.full((4,4),alpha,float); np.fill_diagonal(a,0.)
    if kind=='aniso':
        a[1:,0]=0.
    if kind=='fine':
        a[:]=0.
    return a

# ---------- free field ----------
def kernel(k,sp,a):
    ph=np.exp(1j*k*sp); B=np.zeros(k.shape[:-1]+(4,4),complex)
    for m in range(4):
        line=1+ph[...,m]; B[...,m,m]+=line
        for n in range(4):
            if n==m or a[m,n]==0: continue
            B[...,m,m]+=a[m,n]*ph[...,n]*line
            B[...,m,n]+=a[m,n]*(1-ph[...,m]**2)
            pb=np.conj(ph[...,n])
            B[...,m,m]+=a[m,n]*pb*line
            B[...,m,n]+=a[m,n]*pb*(ph[...,m]**2-1)
        B[...,m,:]/=1+2*a[m].sum()
    return B

def kernel_half(k,sp,alpha):
    """First link raw, second link averaged with lower staples that avoid every first link.
    That this map has an exact density is a hand observation, not formalized. It still roughens here."""
    ph=np.exp(1j*k*sp); B=np.zeros(k.shape[:-1]+(4,4),complex); c=1+3*alpha
    for m in range(4):
        B[...,m,m]+=1+ph[...,m]/c
        for n in range(4):
            if n==m: continue
            pb=np.conj(ph[...,n])
            B[...,m,m]+=alpha*ph[...,m]*pb/c
            B[...,m,n]+=alpha*pb*ph[...,m]*(ph[...,m]-1)/c
    return B

def free_levels(N,a,jmax,half=None):
    g=2*np.pi*np.arange(N)/N
    k=np.stack(np.meshgrid(g,g,g,g,indexing='ij'),-1).reshape(-1,4)
    k=k[np.any(k!=0,axis=1)]
    khat2=(4*np.sin(k/2)**2).sum(-1)
    B=np.tile(np.eye(4,dtype=complex),(k.shape[0],1,1))
    sp,te=[],[]
    for j in range(jmax+1):
        s=2**j; D=np.exp(1j*k*s)-1; ts=tt=0.
        for m in range(4):
            for n in range(m+1,4):
                f=D[...,m,None]*B[:,n,:]-D[...,n,None]*B[:,m,:]
                v=float(3*((np.abs(f)**2).sum(-1)/(2*khat2)).sum()/N**4)
                if m==0: tt+=v/3
                else: ts+=v/3
        sp.append(ts); te.append(tt)
        if j<jmax: B=(kernel_half(k,s,half) if half is not None else kernel(k,s,a))@B
    return sp,te

def mode_free(out,N):
    res={}
    for kind in ('iso','aniso'):
        for alpha in (0.,0.1,0.15,0.25,0.5,1.0):
            a=weights(kind,alpha); sp,te=free_levels(N,a,int(np.log2(N))-2)
            rs=[round(sp[i+1]/sp[i],3) for i in range(len(sp)-1)]; rt=[round(te[i+1]/te[i],3) for i in range(len(te)-1)]
            res[f'{kind}_{alpha}']=dict(spatial=sp,temporal=te,ratio_spatial=rs,ratio_temporal=rt)
            print(kind,alpha,'spatial',rs,'temporal',rt,flush=True)
    for alpha in (0.,0.15,0.25,0.5,1.0,2.0,5.0):
        sp,te=free_levels(N,None,int(np.log2(N))-2,half=alpha)
        rs=[round(sp[i+1]/sp[i],3) for i in range(len(sp)-1)]
        res[f'half_{alpha}']=dict(spatial=sp,temporal=te,ratio_spatial=rs,ratio_temporal=[round(te[i+1]/te[i],3) for i in range(len(te)-1)])
        print('half',alpha,'ratio',rs,flush=True)
    json.dump(dict(N=N,levels=res),open(out,'w'),indent=1)

def hankel_winding(L,T,a):
    """C(s) of the coarse winding: A^i colour, k1=0, k2=pi/L mod pi, k3 = 0 mod pi; aliases of the coarse sum included."""
    k0=2*np.pi*np.arange(T)/T
    tot=np.zeros(5)
    for e1 in (0,np.pi):
        for e2 in (0,np.pi):
            for e3 in (0,np.pi):
                k=np.zeros((T,4)); k[:,0]=k0; k[:,1]=e1; k[:,2]=np.pi/L+e2; k[:,3]=e3
                khat2=(4*np.sin(k/2)**2).sum(-1)
                B=kernel(k,1,a) if a is not None else None
                amp=np.abs(B[:,1,1])**2+sum(np.abs(B[:,1,n])**2 for n in (0,2,3))
                for s in range(5):
                    tot[s]+=float(((amp/(2*khat2))*np.cos(k0*2*s)).sum()/T)
    return tot

def hankel_f12(L,T,a):
    """Untwisted free F12 on the coarse lattice, each coarse spatial momentum, aliases included. Returns worst ratio C0 C2/C1^2."""
    k0=2*np.pi*np.arange(T)/T; g=2*np.pi*np.arange(L//2)/L; worst=(np.inf,None); out=[]; opn=[]
    for q1 in g:
        for q2 in g:
            for q3 in g:
                if q1==0 and q2==0: continue
                tot=np.zeros(5)
                for e1 in (0,np.pi):
                    for e2 in (0,np.pi):
                        for e3 in (0,np.pi):
                            k=np.zeros((T,4)); k[:,0]=k0; k[:,1]=q1+e1; k[:,2]=q2+e2; k[:,3]=q3+e3
                            if q1+e1==0 and q2+e2==0 and q3+e3==0: k=k[1:]
                            khat2=(4*np.sin(k/2)**2).sum(-1)
                            B=kernel(k,1,a); D=np.exp(2j*k)-1
                            f=D[:,1,None]*B[:,2,:]-D[:,2,None]*B[:,1,:]
                            amp=(np.abs(f)**2).sum(-1)
                            for s in range(5):
                                tot[s]+=float(((amp/(2*khat2))*np.cos(k[:,0]*2*s)).sum()/T)
                if tot[1]**2>0 and tot[0]>0:
                    r=tot[0]*tot[2]/tot[1]**2
                    out.append(r); opn.append(tot[2]*tot[4]/tot[3]**2)
                    if r<worst[0]: worst=(r,(q1,q2,q3))
    return worst,float(np.mean(np.array(out)<1-1e-9)),len(out),float(np.min(opn))

def mode_hankel(out,L):
    T=8*L; res={}
    # exact free winding ratios on the hypercubic lattice T = L and on T = 3 L, for comparison with the heatbath runs
    refs={}
    for kind,alpha in (('iso',0.01),('iso',0.05),('iso',0.1),('iso',0.15),('iso',1/6),('iso',0.16),('iso',0.25),('aniso',0.15),('aniso',0.25),('fine',0.)):
        for TT in (L,3*L):
            c=hankel_winding(L,TT,weights(kind,alpha))
            refs[f'{kind}_{alpha}_T{TT}']=float(r_one(c))
            if TT==L: refs[f'{kind}_{alpha}_T{TT}_two_slices']=float(r_two(c))
    res_refs=refs
    for kind in ('iso','aniso'):
        for alpha in (0.,0.01,0.02,0.05,0.1,0.15,0.25,0.5,1.0):
            a=weights(kind,alpha)
            c=hankel_winding(L,T,a); r=c[0]*c[2]/c[1]**2; ro=c[2]*c[4]/c[3]**2
            (w,q),frac,cnt,wo=hankel_f12(L,4*L,a)
            res[f'{kind}_{alpha}']=dict(C=c.tolist(),ratio=float(r),ratio_open=float(ro),f12_worst=float(w),f12_fraction_below_1=frac,f12_modes=cnt,f12_open_worst=wo)
            print(kind,alpha,'winding C0C2/C1^2 =',round(float(r),4),'C2C4/C3^2 =',round(float(ro),4),' F12 worst',round(float(w),4),'open worst',round(wo,4),'frac<1',round(frac,3),'of',cnt,flush=True)
    json.dump(dict(L=L,T=T,note='RP requires ratio >= 1; exact free values, not a proof. f12 modes are all coarse spatial momenta with (q1,q2) != 0, not a subset.',res=res,winding_refs=res_refs),open(out,'w'),indent=1)

# ---------- heatbath ----------
def qmul(a,b):
    w1,x1,y1,z1=a[...,0],a[...,1],a[...,2],a[...,3]; w2,x2,y2,z2=b[...,0],b[...,1],b[...,2],b[...,3]
    return np.stack([w1*w2-x1*x2-y1*y2-z1*z2,w1*x2+x1*w2+y1*z2-z1*y2,w1*y2-x1*z2+y1*w2+z1*x2,w1*z2+x1*y2-y1*x2+z1*w2],-1)
CONJ=np.array([1.,-1,-1,-1])
def qc(a): return a*CONJ
def S(f,m,k=1): return np.roll(f,-k,axis=m)
def zz(z,m,n): return z if {m,n}=={1,2} else 1.

def staple(U,z,m):
    tot=0.
    for n in range(4):
        if n==m: continue
        s=zz(z,m,n)
        up=qmul(qmul(S(U[n],m),qc(S(U[m],n))),qc(U[n]))
        bk=qmul(qmul(qc(S(U[n],m)),qc(U[m])),U[n])
        if not np.isscalar(s):
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

def block(U,z,a):
    out=[]
    for m in range(4):
        line=qmul(U[m],S(U[m],m)); tot=line.copy()
        for n in range(4):
            if n==m or a[m,n]==0: continue
            s=zz(z,m,n)
            sg_up=s*S(s,m) if not np.isscalar(s) else 1.
            up=qmul(qmul(U[n],S(line,n)),qc(S(U[n],m,2)))
            if not np.isscalar(sg_up): up=up*sg_up[...,None]
            un=S(U[n],n,-1)
            dn=qmul(qmul(qc(un),S(line,n,-1)),S(un,m,2))
            if not np.isscalar(sg_up): dn=dn*S(sg_up,n,-1)[...,None]
            tot=tot+a[m,n]*(up+dn)
        V=tot/np.linalg.norm(tot,axis=-1,keepdims=True)
        out.append(V)
    return out

def winding(V1,step,t_idx):
    """trW1 = 2 Re of the product along direction 1 from x1 = 0 of links spaced `step`, as an array (t,x2,x3) on coarse sites."""
    v=V1[t_idx][:,:,::step,::step] if step>1 else V1[t_idx]
    L1=v.shape[1]
    w=v[:,0]
    for i in range(step,L1,step):
        w=qmul(w,v[:,i])
    return 2*w[...,0]

def project(w,L,step):
    """k3 = 0, k2 = pi/L. trW1 is smooth on x2 = 1..L across the twist (the sign flip sits on the link x2 = 0 -> 1)."""
    x2=np.arange(0,L,step).astype(float); x2[0]=L   # x2 = 0 is the end of the smooth interval
    c=np.cos(np.pi*x2/L); s=np.sin(np.pi*x2/L)
    W=w.sum(-1)
    return (W*c).sum(-1),(W*s).sum(-1)

def tau_int(x):
    """Integrated autocorrelation time with the usual automatic window, in units of measurements."""
    x=x-x.mean(); n=len(x); f=np.fft.rfft(x,2*n); c=np.fft.irfft(f*np.conj(f))[:n]/np.arange(n,0,-1); c=c/c[0]
    t=.5
    for W in range(1,n//4):
        t+=c[W]
        if W>=6*t: break
    return float(t)

def r_one(c): return c[...,0]*c[...,2]/c[...,1]**2
def r_two(c):
    """Two reflection slices, coarse T = 4: the block (u, v) with u = (O0 + O2)/sqrt 2, v = O1 of the matrix C(s + t). RP needs >= 1.
    A single transfer-matrix mode gives exactly 1. Use this one on T = L, where C2 also has its periodic image."""
    return (c[...,0]+c[...,2])*c[...,2]/(2*c[...,1]**2)

def jack_err(E,nb,f=r_one):
    b=np.array_split(E,nb); M=np.array([x.mean(0) for x in b])
    J=np.array([np.delete(M,i,0).mean(0) for i in range(nb)])
    r=f(J)
    return float(np.sqrt((nb-1)*((r-r.mean())**2).sum()/nb))

def ratio_of(E,f=r_one): return float(f(E.mean(0)))

def mode_mc(out,L,T,bstd,maps,nt,nm,seed):
    par=np.indices((T,L,L,L)).sum(0)%2
    z0=np.ones((T,L,L,L)); z0[:,0,0,:]=-1
    A={}
    for spec in maps.split(','):
        k,al=spec.split(':'); A[spec]=weights(k,float(al))
    ts=np.arange(0,T,2)
    rng=np.random.default_rng(seed)
    U=np.zeros((4,T,L,L,L,4)); U[...,0]=1
    U[1][:,0,:,:]=np.array([0.,1,0,0]); U[2][:,:,0,:]=np.array([0.,0,1,0])
    beta=bstd/2
    def upd():
        heat(U,z0,beta,rng,par)
        for _ in range(3): over(U,z0,par)
    for _ in range(nt): upd()
    rec={k:[] for k in A}; pl=[]
    def save():
        res=dict(L=L,T=T,beta_std=bstd,beta_lean=beta,seed=seed,ntherm=nt,nmeas=len(pl),updates_per_meas=2,
                 update='one heatbath sweep plus three overrelaxation sweeps',start='flat twisted field',
                 hypercubic_as_in_lean=(T==L),plaq12_mean=float(np.mean(pl)),tau_plaq12=tau_int(np.array(pl)) if len(pl)>16 else None,maps={})
        for k,v in rec.items():
            E=np.array(v); n=len(E)
            nbs=[b for b in (n,400,200,100,40,20,10) if b<=n]
            res['maps'][k]=dict(C=E.mean(0).tolist(),ratio=ratio_of(E),err_by_nbins={str(b):jack_err(E,b) for b in nbs},
                                tau=[tau_int(E[:,i]) for i in range(E.shape[1])] if n>16 else None,
                                half1=ratio_of(E[:n//2]),half2=ratio_of(E[n//2:]))
            if T==L:
                res['maps'][k].update(ratio_two_slices=ratio_of(E,r_two),err_two_slices_by_nbins={str(b):jack_err(E,b,r_two) for b in nbs},
                                      half1_two=ratio_of(E[:n//2],r_two),half2_two=ratio_of(E[n//2:],r_two))
        json.dump(res,open(out,'w'),indent=1)
        return res
    for im in range(nm):
        upd(); upd()
        for k,a in A.items():
            V=block(U,z0,a); w=winding(V[1],2,ts); pc,ps=project(w,L,2)
            rec[k].append([float((pc*np.roll(pc,-s)+ps*np.roll(ps,-s)).mean()) for s in range(3)])
        P=qmul(qmul(qmul(U[1],S(U[2],1)),qc(S(U[1],2))),qc(U[2]))[...,0]*z0
        pl.append(float(P.mean()))
        if (im+1)%200==0:
            save(); print(im+1,flush=True)
    r=save(); print(json.dumps({k:(round(v['ratio'],4),v['err_by_nbins']) for k,v in r['maps'].items()}),flush=True)

# ---------- rank of the differential ----------
def mode_rank(out,N,alpha,nconf):
    res=[]; rng=np.random.default_rng(N+int(1000*alpha))
    z0=np.ones((N,)*4); z0[:,0,0,:]=-1
    h=1e-6
    for kind in ('iso','aniso'):
        a=weights(kind,alpha)
        for ic in range(nconf+1):
            if ic==0:
                U=np.zeros((4,N,N,N,N,4)); U[...,0]=1
                U[1][:,0,:,:]=np.array([0.,1,0,0]); U[2][:,:,0,:]=np.array([0.,0,1,0]); name='flat'
            else:
                U=rng.normal(size=(4,N,N,N,N,4)); U/=np.linalg.norm(U,axis=-1,keepdims=True); name='haar'
            def coarse(W):
                V=block(W,z0,a)
                return np.stack([v[::2,::2,::2,::2] for v in V])
            V0=coarse(U); nc=V0.shape[0]*np.prod(V0.shape[1:-1]); nf=U.shape[0]*np.prod(U.shape[1:-1])
            J=np.zeros((int(3*nc),int(3*nf)),dtype=np.float32)
            idx=0
            for m in range(4):
                for pos in np.ndindex(N,N,N,N):
                    for c in range(3):
                        e=np.zeros(4); e[c+1]=h; e[0]=1
                        keep=U[m][pos].copy()
                        U[m][pos]=qmul(e,keep)
                        V1=coarse(U)
                        U[m][pos]=keep
                        d=qmul(V1,qc(V0))[...,1:]/h
                        J[:,idx]=d.reshape(-1); idx+=1
            sv=np.linalg.svd(J,compute_uv=False)
            r=dict(N=N,alpha=alpha,map=kind,conf=name,coarse_dof=int(3*nc),rank=int((sv>1e-4).sum()),smin=float(sv.min()),smax=float(sv.max()))
            res.append(r); print(json.dumps(r),flush=True)
    json.dump(res,open(out,'w'),indent=1)

def mode_two(out):
    """Reflection-compatible weights: a_ij = s on spatial links, a_0j = t on time links, a_i0 = 0.
    Adm needs 4 s < 1 and 6 t < 1, so (0.24, 0.24) is a comparison point outside the admissible range."""
    res={}
    for s_,t in ((0.24,0.16),(0.2,0.16),(0.16,0.16),(0.24,0.24)):
        a=np.zeros((4,4)); a[1:,1:]=s_; a[0,1:]=t; np.fill_diagonal(a,0.)
        sp,te=free_levels(32,a,3)
        rs=[round(sp[i+1]/sp[i],3) for i in range(3)]; rt=[round(te[i+1]/te[i],3) for i in range(3)]
        c=hankel_winding(8,64,a)
        res[f'{s_}_{t}']=dict(ratio_spatial=rs,ratio_temporal=rt,winding_ratio=float(c[0]*c[2]/c[1]**2),admissible=bool(4*s_<1 and 6*t<1))
        print(s_,t,rs,rt,round(c[0]*c[2]/c[1]**2,4),flush=True)
    json.dump(res,open(out,'w'),indent=1)

def defects(U,tw):
    """Plaquette defects |P - sign| over the planes mu < nu, with the Lean twist: sign -1 in plane (1,2) at x1 = x2 = 0."""
    out={}
    for m in range(4):
        for n in range(m+1,4):
            P=qmul(qmul(qmul(U[m],S(U[n],m)),qc(S(U[m],n))),qc(U[n]))
            T=np.zeros(P.shape); T[...,0]=1.
            if (m,n)==(1,2): T[...,0]=tw
            out[(m,n)]=np.linalg.norm(P-T,axis=-1)
    return out

def mode_interp(out,n,nconf):
    """interp: a fine link at an even coordinate carries the coarse link at the corner (coordinates rounded up); at odd, 1."""
    N=2*n; res=[]; rng=np.random.default_rng(1000+n)
    for ic in range(nconf):
        V=rng.normal(size=(4,n,n,n,n,4)); V/=np.linalg.norm(V,axis=-1,keepdims=True)
        U=np.zeros((4,N,N,N,N,4)); U[...,0]=1.
        for z in np.ndindex(N,N,N,N):
            c=tuple(((zi+1)//2)%n for zi in z)
            for r in range(4):
                if z[r]%2==0: U[r][z]=V[r][c]
        z0=np.ones((N,N,N,N)); z0[:,0,0,:]=-1
        zc=np.ones((n,n,n,n)); zc[:,0,0,:]=-1
        line=np.stack([qmul(U[m],S(U[m],m))[::2,::2,::2,::2] for m in range(4)])
        df=defects(U,z0); dc=defects(V,zc)
        Sf=sum((v**2).sum() for v in df.values()); Sc=sum((v**2).sum() for v in dc.values())
        off=0.
        for (m,nn),v in df.items():
            mask=np.ones((N,N,N,N),bool)
            idx=np.indices((N,N,N,N))
            mask&=(idx[m]%2==0)&(idx[nn]%2==0)
            off=max(off,float(v[~mask].max()))
        r=dict(n=n,conf=ic,line_error=float(np.abs(line-V).max()),S_fine=float(Sf),S_coarse=float(Sc),ratio=float(Sf/Sc),max_defect_off_even_cells=off)
        res.append(r); print(json.dumps(r),flush=True)
    json.dump(res,open(out,'w'),indent=1)

def mode_summ(npz,out):
    """Summarize a saved chain with the same estimators as mode_mc. The array names are the maps; 'pl' is the plaquette series."""
    d=np.load(npz); res=dict(plaq12_mean=float(d['pl'].mean()),tau_plaq12=tau_int(d['pl']),nmeas=int(len(d['pl'])))
    for k in d.files:
        if k=='pl': continue
        E=d[k]; n=len(E); nbs=[b for b in (n,400,200,100,40,20,10) if b<=n]
        res[k]=dict(C=E.mean(0).tolist(),ratio=ratio_of(E),err_by_nbins={str(b):jack_err(E,b) for b in nbs},
                    tau=[tau_int(E[:,i]) for i in range(E.shape[1])],half1=ratio_of(E[:n//2]),half2=ratio_of(E[n//2:]))
    json.dump(res,open(out,'w'),indent=1); print(json.dumps({k:(round(v['ratio'],4),round(v['err_by_nbins']['40'],4)) for k,v in res.items() if isinstance(v,dict)}))

if __name__=='__main__':
    mode=sys.argv[1]
    if mode=='summ': mode_summ(sys.argv[2],sys.argv[3])
    if mode=='interp': mode_interp(sys.argv[2],int(sys.argv[3]),int(sys.argv[4]))
    if mode=='two': mode_two(sys.argv[2])
    if mode=='free': mode_free(sys.argv[2],int(sys.argv[3]))
    elif mode=='hankel': mode_hankel(sys.argv[2],int(sys.argv[3]))
    elif mode=='mc':
        mode_mc(sys.argv[2],int(sys.argv[3]),int(sys.argv[4]),float(sys.argv[5]),sys.argv[6],int(sys.argv[7]),int(sys.argv[8]),int(sys.argv[9]))
    elif mode=='rank': mode_rank(sys.argv[2],int(sys.argv[3]),float(sys.argv[4]),int(sys.argv[5]))
