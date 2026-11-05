"""Covariant block Schur bound on the long modes, matrix-free, for larger blocks (numerics, not a proof).

Same quantity as sig_ir in yang_mills_schur_block.py (COV=1): the configuration-averaged Schur complement of the
covariant block split, restricted to the 12 longest-wavelength coarse directions and normalized by the free Schur
complement there (free field = 1). Only Q^T S Q is needed, so each configuration costs 12 conjugate-gradient solves on the
fine space instead of a sparse factorization; this reaches n = 8. The fine space is handled with the orthogonal
projector P = 1 - C C^T, and the 12 directions are the lowest eigenvectors of the free Schur operator, by LOBPCG.
Purpose: Schur complements compose exactly (integrating out nested fine spaces in two steps or at once gives the same
complement), so a single step with block side l stands in for log2(l) steps. If the covariant scheme composes, sig_ir
stays near 1 as l grows; if transport noise accumulates along longer paths, it falls with l.
Written before any run: sig_ir >= 0.9 at (n, l) = (6, 3), (8, 2), (8, 4), beta_std = 32 and 16.
Usage: out n l beta_stds n_cfg
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, scipy.sparse as sp
from scipy.sparse.linalg import LinearOperator, cg, lobpcg
from yang_mills_preconditioned_hessian import hessian, gauge_D, cool, gauge_fix, rot, idx
from yang_mills_twisted_step_scaling import twist, heat, over, qmul, qc, staple

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
def coarse(N,l):
    I=idx(N); d=4*N**4*3; x=np.indices((N,)*4)
    blk=((x[0]//l)*(N//l)**3+(x[1]//l)*(N//l)**2+(x[2]//l)*(N//l)+x[3]//l).ravel(); nb=(N//l)**4; L=l**4
    order=np.argsort(blk,kind='stable'); rows=[];cols=[]; nc=0
    for m in range(4):
        e=I[m].ravel()
        for b in range(nb):
            links=e[order[b*L:(b+1)*L]]
            for a in range(3): rows+=list(3*links+a); cols+=[nc]*L; nc+=1
    return sp.csr_matrix((np.full(len(rows),1/np.sqrt(L)),(rows,cols)),shape=(d,nc))

def smear(U,z,steps,alpha=0.5):
    """Gauge-covariant smearing: each link -> normalized mix of itself and its local action minimizer qc(A)/|A|.
    Averages the transport over many paths; leaves a flat (twisted) vacuum unchanged."""
    U=U.copy()
    for _ in range(steps):
        new=[]
        for m in range(4):
            A=staple(U,z,m); best=qc(A/np.linalg.norm(A,axis=-1,keepdims=True))
            W=(1-alpha)*U[m]+alpha*best; new.append(W/np.linalg.norm(W,axis=-1,keepdims=True))
        U=np.stack(new)
    return U

class Split:
    """Schur complement of Ht over the fine space range(1 - C C^T), applied matrix-free."""
    def __init__(self,Ht,C,scale):
        self.H=Ht; self.C=C; d=Ht.shape[0]; self.d=d
        P=lambda x: x-C@(C.T@x); self.P=P
        self.A=LinearOperator((d,d),matvec=lambda x: P(Ht@P(x))+scale*(C@(C.T@x)),dtype=float)
        dg=Ht.diagonal(); self.M=LinearOperator((d,d),matvec=lambda x: x/np.maximum(dg,1e-12),dtype=float)
    def fine_solve(self,r):
        x,info=cg(self.A,self.P(r),rtol=1e-9,maxiter=20000,M=self.M)
        if info!=0: print('cg info',info,flush=True)
        return self.P(x)
    def apply(self,u):
        """S u for a coarse vector u."""
        u=np.asarray(u).ravel(); v=self.C@u; Hv=self.H@v
        return self.C.T@Hv-self.C.T@(self.H@self.fine_solve(Hv))
    def quad(self,Q):
        """Q^T S Q for coarse columns Q."""
        V=self.C@Q; HV=self.H@V; X=np.column_stack([self.fine_solve(HV[:,i]) for i in range(Q.shape[1])])
        M=V.T@HV-HV.T@X; return (M+M.T)/2

out=sys.argv[1]; N=int(sys.argv[2]); l=int(sys.argv[3]); bs=[float(x) for x in sys.argv[4].split(',')]
ncfg=int(sys.argv[5]); K=float(os.environ.get('KPEN','100')); ns=int(os.environ.get('SMEAR','0')); res=[]
rng=np.random.default_rng(11+N); z=twist(N); par=np.indices((N,)*4).sum(0)%2
V=np.zeros((4,)+(N,)*4+(4,)); V[...,0]=1
for _ in range(100): heat(V,z,30.,rng,par); over(V,z,par)
cool(V,z,par); D0=gauge_D(V); C=coarse(N,l); G=(K*D0@D0.T).tocsr(); T0=tmat(N,frames(V,l)); nc=C.shape[1]
for b in bs:
    Hv=(T0.T@(hessian(V,z,b)+b*G)@T0).tocsr(); Sv=Split(Hv,C,b)
    Sop=LinearOperator((nc,nc),matvec=Sv.apply,dtype=float)
    w,Qv=lobpcg(Sop,np.random.default_rng(1).normal(size=(nc,16)),largest=False,tol=1e-6,maxiter=300)
    o=np.argsort(w); w=w[o][:12]; Q=Qv[:,o][:,:12]@np.diag(1/np.sqrt(w))
    chk=np.linalg.eigvalsh(Sv.quad(Q))
    print('N',N,'l',l,'bstd',b,'coarse dim',nc,'free Schur low',np.round(w,3).tolist(),'check',round(chk[0],4),round(chk[-1],4),flush=True)
    U=V.copy()
    for _ in range(300): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
    Ms=[]
    for c in range(ncfg):
        for _ in range(20): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
        best=None
        for c0 in (1,-1):
            for c3 in (1,-1):
                W=U.copy(); W[0][0]*=c0; W[3][:,:,:,0]*=c3; Wg,F=gauge_fix(W,V,par)
                if best is None or F>best[1]: best=(Wg,F)
        TU=tmat(N,frames(smear(best[0],z,ns) if ns else best[0],l)); Hu=(TU.T@(hessian(best[0],z,b)+b*G)@TU).tocsr()
        M=Split(Hu,C,b).quad(Q); Ms.append(M)
        print(json.dumps(dict(N=N,l=l,bstd=b,cfg=c,sig_pt=float(np.linalg.eigvalsh(M)[0]))),flush=True)
    A=np.array(Ms); s=float(np.linalg.eigvalsh(A.mean(0))[0])
    jk=np.array([np.linalg.eigvalsh(np.delete(A,i,0).mean(0))[0] for i in range(len(A))])
    row=dict(N=N,l=l,bstd=b,K=K,smear=ns,coarse_dim=nc,sig_ir=s,sig_ir_err=float(np.sqrt((len(A)-1)*((jk-jk.mean())**2).mean())),
             sig_pt_mean=float(np.mean([np.linalg.eigvalsh(m)[0] for m in A])))
    res.append(row); print(json.dumps(row),flush=True); json.dump(res,open(out,'w'))
