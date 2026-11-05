"""Frame-curvature correction to the covariant one-step Schur bound (numerics, not a proof).

yang_mills_schur_block.py (COV=1) rotates the Hessian by the configuration's own block frames T_U and treats T_U as
constant. A coarse direction w is really the vector field Z(U) = T_U w, and the second derivative of the action along
it is <Z, H Z> + <grad S, nabla_Z Z>. The second term, c(w) = <grad S, (d_Z T) w>, was dropped: it is the force (UV noise)
contracted with the turning of the frame. Here w runs over the 12 longest-wavelength coarse directions, normalized so the
free Schur complement is 1, so c(w) is directly the shift of sigma_ir that the frozen frame missed.
(d_Z T) w is a centred finite difference of the frames along exp(delta Z) U; grad S is by autograd (exp(eps) U coords).
Written before any run: the averaged correction matrix on the 12 long modes has |eigenvalues| <= 0.1 and roughly flat from n = 4 to 6. |E[c]| of order 1, or growing with n, would undo
the covariant result.
Usage: out ns beta_stds n_cfg
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, scipy.sparse as sp, torch
from scipy.sparse.linalg import splu
from yang_mills_preconditioned_hessian import hessian, gauge_D, cool, gauge_fix, rot, idx
from yang_mills_twisted_step_scaling import twist, heat, over, qmul, qc
torch.set_default_dtype(torch.float64)

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
def blocks(N,l):
    I=idx(N); d=4*N**4*3; x=np.indices((N,)*4)
    blk=((x[0]//l)*(N//l)**3+(x[1]//l)*(N//l)**2+(x[2]//l)*(N//l)+x[3]//l).ravel(); nb=(N//l)**4; L=l**4
    order=np.argsort(blk,kind='stable'); crow=[];ccol=[];brow=[];bcol=[];bval=[]; nc=0; nf=0
    for m in range(4):
        e=I[m].ravel()
        for b in range(nb):
            links=e[order[b*L:(b+1)*L]]
            for a in range(3):
                crow+=list(3*links+a); ccol+=[nc]*L; nc+=1
                for j in range(1,L): brow+=[3*links[j]+a,3*links[0]+a]; bcol+=[nf,nf]; bval+=[1.,-1.]; nf+=1
    return (sp.csr_matrix((np.full(len(crow),1/np.sqrt(L)),(crow,ccol)),shape=(d,nc)),
            sp.csr_matrix((bval,(brow,bcol)),shape=(d,nf)))
def schur(Ht,C,B):
    lu=splu((B.T@Ht@B).tocsc(),permc_spec='COLAMD'); HC=Ht@C
    Hcc=(C.T@HC).toarray(); Hfc=(B.T@HC).toarray(); S=Hcc-Hfc.T@lu.solve(Hfc); return (S+S.T)/2

def tq(a,b):
    w1,x1,y1,z1=a.unbind(-1); w2,x2,y2,z2=b.unbind(-1)
    return torch.stack([w1*w2-x1*x2-y1*y2-z1*z2,w1*x2+x1*w2+y1*z2-z1*y2,w1*y2-x1*z2+y1*w2+z1*x2,w1*z2+x1*y2-y1*x2+z1*w2],-1)
CJ=torch.tensor([1.,-1,-1,-1])
def texp(a):
    th=torch.sqrt((a*a).sum(-1,keepdim=True)+1e-300)
    return torch.cat([torch.cos(th),torch.where(th>1e-8,torch.sin(th)/th,1-th*th/6)*a],-1)
def grad_action(U,z,b):
    """grad of b * sum_p (1 - z P0) in exp(eps) U coordinates, flattened like the Hessian (link-major, 3 per link)."""
    Ut=torch.tensor(U); zt=torch.tensor(z); eps=torch.zeros(Ut.shape[:-1]+(3,),requires_grad=True); W=tq(texp(eps),Ut); S=0.
    for m in range(4):
        for k in range(m+1,4):
            P=tq(tq(tq(W[m],torch.roll(W[k],-1,m)),torch.roll(W[m],-1,k)*CJ),W[k]*CJ)
            S=S+(1-(zt if {m,k}=={1,2} else 1.)*P[...,0]).sum()
    g,=torch.autograd.grad(b*S,eps); return g.numpy()
def move(U,v,delta):
    """exp(delta v) U with v flattened (link-major)."""
    vt=torch.tensor(v.reshape(U.shape[:-1]+(3,))*delta); return tq(texp(vt),torch.tensor(U)).numpy()

out=sys.argv[1]; ns=[int(x) for x in sys.argv[2].split(',')]; bs=[float(x) for x in sys.argv[3].split(',')]
ncfg=int(sys.argv[4]); K=100.; l=2; dl=1e-4; res=[]
I0=None
for N in ns:
    rng=np.random.default_rng(11+N); z=twist(N); par=np.indices((N,)*4).sum(0)%2
    V=np.zeros((4,)+(N,)*4+(4,)); V[...,0]=1
    for _ in range(100): heat(V,z,30.,rng,par); over(V,z,par)
    cool(V,z,par); D0=gauge_D(V); d=4*N**4*3; C,B=blocks(N,l); G=(K*D0@D0.T).tocsr(); T0=tmat(N,frames(V,l))
    # check that idx flattening matches the (4,N,N,N,N,3) layout used by grad_action / move
    assert np.array_equal(idx(N)[0].ravel(),np.arange(N**4)) and np.array_equal(idx(N)[1].ravel(),N**4+np.arange(N**4))
    for b in bs:
        Sf=schur((T0.T@(hessian(V,z,b)+b*G)@T0).tocsr(),C,B); wS,QS=np.linalg.eigh(Sf)
        Wc=C@(QS[:,:12]@np.diag(1/np.sqrt(wS[:12])))      # long coarse directions in eta coords, free Schur = 1
        U=V.copy()
        for _ in range(300): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
        cs=[]
        for c in range(ncfg):
            for _ in range(20): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
            best=None
            for c0 in (1,-1):
                for c3 in (1,-1):
                    W=U.copy(); W[0][0]*=c0; W[3][:,:,:,0]*=c3; Wg,F=gauge_fix(W,V,par)
                    if best is None or F>best[1]: best=(Wg,F)
            Ug=best[0]; g=grad_action(Ug,z,b).ravel(); TU=tmat(N,frames(Ug,l)); Wd=np.asarray(Wc.todense() if sp.issparse(Wc) else Wc); M=np.zeros((12,12))
            for k in range(12):
                Z=TU@Wd[:,k]
                Tp=tmat(N,frames(move(Ug,Z,dl),l)); Tm=tmat(N,frames(move(Ug,Z,-dl),l))
                M[k]=g@(((Tp-Tm)/(2*dl))@Wd)          # M[k,l] = <grad S, (d_{Z_k} T) w_l>
            M=(M+M.T)/2; ev=np.linalg.eigvalsh(M); cs.append(M)
            print(json.dumps(dict(N=N,bstd=b,cfg=c,eig_min=float(ev[0]),eig_max=float(ev[-1]))),flush=True)
        A=np.array(cs); evm=np.linalg.eigvalsh(A.mean(0))
        out_r=dict(N=N,bstd=b,avg_eig_min=float(evm[0]),avg_eig_max=float(evm[-1]),
                   pt_eig_min=float(np.mean([np.linalg.eigvalsh(m)[0] for m in A])),rms=float(np.sqrt((A**2).mean())))
        res.append(out_r); print(json.dumps({k:v for k,v in out_r.items() }),flush=True); json.dump(res,open(out,'w'))
