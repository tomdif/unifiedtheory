"""Preconditioned Bakry-Emery test for step 4 on the twisted lattice (numerics, not a proof).

Idea. Step 4 needs a neutral gap of order 1/n at beta ~ b log n. A Helffer-Sjostrand / Brascamp-Lieb covariance bound gives
exponential decay at rate ~ m if Hess U + Ric >= c * beta_std * Delta_0 on horizontal directions, where Delta_0 is the
twisted flat Hodge Laplacian (lowest eigenvalue ~ (pi/n)^2, so decay rate ~ 1/n). The perturbation
Delta_0^{-1/2} (Hess U - beta Delta_0) Delta_0^{-1/2} is critical in 4D: first order ~ g sqrt(log n), second order
~ g^2 log n. Both are O(1/sqrt b) or O(1/b) on beta = b log n. So the inequality could hold on typical configurations
exactly in the TargetAGap regime. This script tests that claim (lemma L1). It does not touch the large-field lemma L2.

Measured: lam(U) = smallest generalized eigenvalue of H(U) = Hess U + beta_std D_U D_U^T + 2 I against beta_std Delta_0,
with U in background Landau gauge relative to a flat twisted vacuum V (best of the four center sectors). 2 I is the
Ricci curvature of SU(2) = unit S^3 per link. D_U D_U^T is the gauge-fixing term; at V it turns Hess into the Hodge form.

Written before any run:
  Bug check: at U = V, lam = 1 + 2/(beta_std * max eig Delta_0) > 1.
  L1 alive: at fixed beta_std, 1 - lam grows no faster than log n from n = 4 to 8 (critical scaling), and lam > 1/2
            along some line beta_std = b log n.
  L1 dead:  lam < 0 for all tested beta_std at n = 8, or 1 - lam grows like a power of n at fixed beta_std.
Usage: out ns beta_stds n_cfg
"""
import os, sys, json, time
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, scipy.sparse as sp, scipy.linalg as sl
from scipy.sparse.linalg import lobpcg, LinearOperator, cg
from yang_mills_twisted_step_scaling import qmul, qc, S, twist, zz, heat, over, energy, staple

def rot(q):
    w,x,y,z=q[...,0],q[...,1],q[...,2],q[...,3]
    return np.stack([np.stack([1-2*(y*y+z*z),2*(x*y-w*z),2*(x*z+w*y)],-1),
                     np.stack([2*(x*y+w*z),1-2*(x*x+z*z),2*(y*z-w*x)],-1),
                     np.stack([2*(x*z-w*y),2*(y*z+w*x),1-2*(x*x+y*y)],-1)],-2)
def skew(p):
    o=np.zeros(p.shape[:-1]+(3,3))
    o[...,0,1]=-p[...,2]; o[...,0,2]=p[...,1]; o[...,1,0]=p[...,2]; o[...,1,2]=-p[...,0]; o[...,2,0]=-p[...,1]; o[...,2,1]=p[...,0]
    return o

def idx(N):
    return np.arange(4*N**4).reshape(4,N,N,N,N)

def hessian(U,z,bstd):
    """Hess of -(bstd/2) sum z Re tr P in coordinates exp(eps) U_e, eps in R^3 per link (unit S^3 metric)."""
    N=U.shape[1]; I=idx(N); rows=[]; cols=[]; vals=[]
    for m in range(4):
        for n in range(m+1,4):
            s=zz(z,m,n); s=s if not np.isscalar(s) else np.ones((N,)*4)
            U1,U2,U3,U4=U[m],S(U[n],m),S(U[m],n),U[n]
            W3=qmul(qmul(U1,U2),qc(U3)); P=qmul(W3,qc(U4))
            R=[np.broadcast_to(np.eye(3),(N,)*4+(3,3)),rot(U1),-rot(W3),-rot(P)]
            ids=[I[m],S(I[n],m),S(I[m],n),I[n]]
            c=bstd*s; P0=P[...,0]; K=skew(P[...,1:])
            for i in range(4):
                for j in range(4):
                    Ri=np.swapaxes(R[i],-1,-2)
                    B=P0[...,None,None]*(Ri@R[j])
                    if i<j: B=B-Ri@K@R[j]
                    elif i>j: B=B+Ri@K@R[j]   # transpose of the i<j block: (R_j^T K R_i)^T = -R_i^T K R_j
                    B=c[...,None,None]*B
                    a=ids[i].ravel(); b=ids[j].ravel(); Bf=B.reshape(-1,3,3)
                    for p in range(3):
                        for q in range(3):
                            rows.append(3*a+p); cols.append(3*b+q); vals.append(Bf[:,p,q])
    d=4*N**4*3
    return sp.csr_matrix((np.concatenate(vals),(np.concatenate(rows),np.concatenate(cols))),shape=(d,d))

def gauge_D(U):
    """(D w)_e = w_x - Ad(U_e) w_{x+mu}: sites (3 per) -> links (3 per)."""
    N=U.shape[1]; site=np.arange(N**4).reshape((N,)*4); rows=[]; cols=[]; vals=[]; I=idx(N)
    for m in range(4):
        e=I[m].ravel(); x=site.ravel(); y=S(site,m).ravel(); R=rot(U[m]).reshape(-1,3,3)
        for p in range(3):
            rows.append(3*e+p); cols.append(3*x+p); vals.append(np.ones(e.size))
            for q in range(3):
                rows.append(3*e+p); cols.append(3*y+q); vals.append(-R[:,p,q])
    return sp.csr_matrix((np.concatenate(vals),(np.concatenate(rows),np.concatenate(cols))),shape=(4*N**4*3,N**4*3))

def cool(U,z,par,tol=1e-13,maxit=20000):
    for it in range(maxit):
        over(U,z,par)
        for m in range(4):
            for p in (0,1):
                A=staple(U,z,m); nrm=np.linalg.norm(A,axis=-1); mask=par==p
                U[m][mask]=qc(A[mask]/nrm[mask][:,None])
        if it%50==0 and energy(U,z)<tol: break
    return energy(U,z)

def gauge_fix(U,V,par,sweeps=4000,omega=1.7):
    """Maximize sum_e scalar(g_x U_e g_{x+mu}^-1 V_e^-1) by overrelaxed site updates. Returns (U', functional)."""
    U=U.copy(); N=U.shape[1]
    for it in range(sweeps):
        for p in (0,1):
            K=np.zeros((N,)*4+(4,))
            for m in range(4):
                K+=qmul(U[m],qc(V[m]))
                K+=S(qmul(qc(U[m]),V[m]),m,-1)
            h=qc(K); h/=np.linalg.norm(h,axis=-1,keepdims=True)
            # overrelax: h^omega approximated by normalized (1-omega) 1 + omega h
            h2=np.zeros_like(h); h2[...,0]=1-omega; h2+=omega*h; h2/=np.linalg.norm(h2,axis=-1,keepdims=True)
            g=np.where((par==p)[...,None],h2,np.array([1.,0,0,0]))
            for m in range(4): U[m]=qmul(qmul(g,U[m]),qc(S(g,m)))
        if it%100==0:
            F=sum(qmul(U[m],qc(V[m]))[...,0].mean() for m in range(4))/4
            if it>0 and F-Fold<1e-12: break
            Fold=F
    F=sum(qmul(U[m],qc(V[m]))[...,0].mean() for m in range(4))/4
    return U,float(F)

def lam_min(H,M,Minv,d,dense):
    if dense:
        w=sl.eigh(H.toarray(),M.toarray(),eigvals_only=True,subset_by_index=[0,0]); return float(w[0])
    rng=np.random.default_rng(0); X=rng.normal(size=(d,4))
    w,_=lobpcg(H,X,B=M,M=Minv,largest=False,tol=1e-7,maxiter=600); return float(w.min())

def main():
    out=sys.argv[1]; ns=[int(x) for x in sys.argv[2].split(',')]; bs=[float(x) for x in sys.argv[3].split(',')]; ncfg=int(sys.argv[4])
    Ks=[float(x) for x in sys.argv[5].split(',')] if len(sys.argv)>5 else [1.]  # gauge-term weight; K -> infinity restricts to horizontal
    res=[]
    for N in ns:
        rng=np.random.default_rng(7+N); z=twist(N); par=np.indices((N,)*4).sum(0)%2
        V=np.zeros((4,)+(N,)*4+(4,)); V[...,0]=1
        for _ in range(100): heat(V,z,30.,rng,par); over(V,z,par)
        eV=cool(V,z,par); print('N',N,'flat action',eV,flush=True)
        H0=hessian(V,z,1.); D0=gauge_D(V); Delta0=(H0+D0@D0.T).tocsr()
        d=Delta0.shape[0]; dense=d<=4000
        if dense:
            ev=sl.eigh(Delta0.toarray(),eigvals_only=True); lo,hi=ev[0],ev[-1]
        else:
            # top of band by power iteration (ARPACK stalls on the degenerate top); bottom is the twisted shift 4 sin^2(pi/2N)
            x=np.random.default_rng(1).normal(size=d)
            for _ in range(300): x=Delta0@x; x/=np.linalg.norm(x)
            hi=float(x@(Delta0@x)); lo=float(4*np.sin(np.pi/(2*N))**2)
        print('N',N,'Delta0 eig range',lo,hi,flush=True)
        def mk_inv(M):
            def f(x):
                x=np.asarray(x); X=x.reshape(d,-1); Y=np.empty_like(X)
                for k in range(X.shape[1]): Y[:,k]=cg(M,X[:,k],rtol=1e-6,maxiter=500)[0]
                return Y.reshape(x.shape)
            return LinearOperator((d,d),matvec=f,matmat=f)
        for b in bs:
            M=(b*Delta0).tocsr(); Minv=None if dense else mk_inv(M)
            Hv=(hessian(V,z,b)+b*D0@D0.T+2*sp.identity(d)).tocsr()
            check=lam_min(Hv,M,Minv,d,dense)
            U=np.zeros_like(V); U[...]=V
            for _ in range(200): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
            lams=[]; lams_noric=[]; Fs=[]
            for c in range(ncfg):
                for _ in range(40): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
                best=None
                for c0 in (1,-1):
                    for c3 in (1,-1):
                        W=U.copy(); W[0][0]*=c0; W[3][:,:,:,0]*=c3
                        Wg,F=gauge_fix(W,V,par)
                        if best is None or F>best[1]: best=(Wg,F)
                Wg,F=best; Fs.append(F)
                H=hessian(Wg,z,b); D=gauge_D(Wg); row=[]; rown=[]
                for K in Ks:
                    Hg=(H+K*b*D@D.T).tocsr()
                    row.append(lam_min((Hg+2*sp.identity(d)).tocsr(),M,Minv,d,dense)); rown.append(lam_min(Hg,M,Minv,d,dense))
                lams.append(row); lams_noric.append(rown)
                print(json.dumps(dict(N=N,bstd=b,cfg=c,F=F,plaq=1-energy(U,z)/4,K=Ks,lam=lams[-1],lam_noric=lams_noric[-1])),flush=True)
            r=dict(N=N,bstd=b,flat_check=check,flat_pred=1+2/(b*hi),lam=lams,lam_noric=lams_noric,F=Fs,Delta0=[float(lo),float(hi)])
            res.append(r); print(json.dumps(r),flush=True); json.dump(res,open(out,'w'))

if __name__=='__main__': main()
