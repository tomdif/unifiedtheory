"""Large fields in the one-step scheme: how often is a side-2 fine block non-convex? (numerics, not a proof).

Hypothesis (a) of the one-step Schur scheme (README, "One RG step as a Schur complement") needs the fine block convex at
every fine configuration. It must fail where plaquettes are far from flat. What matters is the rate: if a block is
non-convex with probability p(beta) ~ exp(-c beta_std), then all (n/2)^4 blocks are convex with high probability only for
beta_std > (4/c) log n. Compared with the asymptotic-freedom slope in standard units, 2 * 11/(6 pi^2) = 0.371, this
says whether large-field blocks vanish along the TargetAGap trajectory or must be treated separately (Balaban).
For each block: lowest eigenvalue of the action Hessian (covariant frames, background-gauge penalty K) restricted to
that block's fine (zero-mean) directions, everything else held fixed, in units of beta_std (only the sign matters for (a); ratios across frames are contaminated by the gauge penalty).
Written before any run: blocks are convex at beta_std >= 8 in every sample; the non-convex fraction rises steeply below
beta_std ~ 4-5; the fitted c gives 4/c > 0.371, so large-field blocks persist at the critical slope.
Usage: out n beta_stds n_cfg
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, scipy.sparse as sp, scipy.linalg as sl
from yang_mills_preconditioned_hessian import hessian, gauge_D, cool, gauge_fix, rot, idx
from yang_mills_twisted_step_scaling import twist, heat, over, qmul, qc

def frames(V,l):
    N=V.shape[1]; W=np.zeros((N,)*4+(4,)); W[...,0]=1
    for nu in range(4):
        for k in range(1,l):
            a=[slice(None)]*4; b=[slice(None)]*4; a[nu]=slice(k,N,l); b[nu]=slice(k-1,N,l)
            W[tuple(a)]=qmul(qc(V[nu][tuple(b)]),W[tuple(b)])
    return rot(W)
def tmat(N,R):
    I=idx(N); d=4*N**4*3; rows=[];cols=[];vals=[]; Rf=R.reshape(-1,3,3)
    for m in range(4):
        e=I[m].ravel()
        for p in range(3):
            for q in range(3): rows.append(3*e+p); cols.append(3*e+q); vals.append(Rf[:,p,q])
    return sp.csr_matrix((np.concatenate(vals),(np.concatenate(rows),np.concatenate(cols))),shape=(d,d))
def block_fine_bases(N,l):
    """For each block: orthonormal basis (dense d x k) of its zero-mean directions, per direction and color."""
    I=idx(N); x=np.indices((N,)*4); L=l**4
    blk=((x[0]//l)*(N//l)**3+(x[1]//l)*(N//l)**2+(x[2]//l)*(N//l)+x[3]//l).ravel(); order=np.argsort(blk,kind='stable')
    # orthonormal basis of zero-mean vectors in R^L (Helmert)
    Hm=sl.null_space(np.ones((1,L)))
    out=[]
    for b in range((N//l)**4):
        dofs=[]; cols=[]
        for m in range(4):
            links=I[m].ravel()[order[b*L:(b+1)*L]]
            for a in range(3): dofs.append(3*links+a)
        out.append(dofs)
    return out,Hm

b_now=[1.]
def block_min_eigs(Ht,Hv,dofs_list,Hm):
    res=[]
    for dofs in dofs_list:
        allidx=np.concatenate(dofs); k=len(dofs)
        Hs=Ht[allidx][:,allidx].toarray(); H0=Hv[allidx][:,allidx].toarray()
        # fine basis: block-diagonal Helmert per (direction, color)
        Bf=sl.block_diag(*([Hm]*k))
        A=Bf.T@Hs@Bf; A0=Bf.T@H0@Bf
        res.append(float(sl.eigh(A,eigvals_only=True,subset_by_index=[0,0])[0])/b_now[0])
    return res

out=sys.argv[1]; N=int(sys.argv[2]); bs=[float(x) for x in sys.argv[3].split(',')]; ncfg=int(sys.argv[4]); l=2
K=100.; res=[]
rng=np.random.default_rng(23+N); z=twist(N); par=np.indices((N,)*4).sum(0)%2
V=np.zeros((4,)+(N,)*4+(4,)); V[...,0]=1
for _ in range(100): heat(V,z,30.,rng,par); over(V,z,par)
cool(V,z,par); D0=gauge_D(V); G=(K*D0@D0.T).tocsr(); dofs_list,Hm=block_fine_bases(N,l)
T0=tmat(N,frames(V,l)); Hv1=(T0.T@(hessian(V,z,1.)+G)@T0).tocsr()
for b in bs:
    Hv=Hv1*b; b_now[0]=b
    U=V.copy()
    for _ in range(300): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
    lams=[]
    for c in range(ncfg):
        for _ in range(20): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
        best=None
        for c0 in (1,-1):
            for c3 in (1,-1):
                W=U.copy(); W[0][0]*=c0; W[3][:,:,:,0]*=c3; Wg,F=gauge_fix(W,V,par)
                if best is None or F>best[1]: best=(Wg,F)
        TU=tmat(N,frames(best[0],l)); Ht=(TU.T@(hessian(best[0],z,b)+b*G)@TU).tocsr()
        lams+=block_min_eigs(Ht,Hv,dofs_list,Hm)
    L=np.array(lams)
    row=dict(N=N,bstd=b,blocks=len(L),frac_nonconvex=float((L<=0).mean()),frac_below_0p25=float((L<0.25).mean()),
             lam_min=float(L.min()),lam_q01=float(np.quantile(L,0.01)),lam_median=float(np.median(L)),raw=L.tolist())
    res.append(row); print(json.dumps({k:v for k,v in row.items() if k!="raw"}),flush=True); json.dump(res,open(out,'w'))
