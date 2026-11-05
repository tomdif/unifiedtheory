"""Covariant block fluctuation form on the twisted lattice (numerics, not a proof).

Q(X) = Hess_U(X)/beta + ||div_U X||^2 + L^-2 sum_nu ||A_U X_nu||^2, where Hess is the exact second
derivative of the action along exp(tX) U, D = T - 1 with T the U-covariant shift, and A_U is the
ordered product of running averages over L steps in each direction. Reports the lowest eigenvalue.
Question: does lambda_min * L^2 depend on N, on chord distance from flat, or on plaquette defect?
"""
import os
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='2'
import sys, json, torch, numpy as np
from scipy.sparse.linalg import LinearOperator, eigsh
torch.set_num_threads(2); torch.set_num_interop_threads(1); torch.set_default_dtype(torch.float64)

def qmul(a, b):
    w1,x1,y1,z1 = a.unbind(-1); w2,x2,y2,z2 = b.unbind(-1)
    return torch.stack([w1*w2-x1*x2-y1*y2-z1*z2, w1*x2+x1*w2+y1*z2-z1*y2,
                        w1*y2-x1*z2+y1*w2+z1*x2, w1*z2+x1*y2-y1*x2+z1*w2], -1)
def qinv(a): return a*torch.tensor([1.,-1,-1,-1])
def qexp(v):
    """exp of imaginary quaternion field v[...,3]"""
    n = v.norm(dim=-1, keepdim=True).clamp_min(1e-300)
    return torch.cat([torch.cos(n), torch.sinc(n/np.pi)*v], -1)
def ad(u, v):
    return qmul(qmul(u, v), qinv(u))
def S(f, mu): return torch.roll(f, -1, dims=mu)   # f(x+mu)
def Sb(f, mu): return torch.roll(f, 1, dims=mu)   # f(x-mu)
def imq(X): return torch.cat([torch.zeros_like(X[...,:1]), X], -1)

def flat(N):
    U = torch.zeros(4, N, N, N, N, 4); U[...,0] = 1
    idx=[slice(None)]*4; idx[1]=0
    U[1][tuple(idx)] = torch.tensor([0.,1,0,0])
    idx=[slice(None)]*4; idx[2]=0
    U[2][tuple(idx)] = torch.tensor([0.,0,1,0])
    return U

def smooth_gauge(N, amp, seed):
    g = torch.Generator().manual_seed(seed)
    grid = torch.meshgrid(*[torch.arange(N, dtype=torch.float64)]*4, indexing='ij')
    v = torch.zeros(N,N,N,N,3)
    for c in range(3):
        for _ in range(3):
            k = torch.randint(-1, 2, (4,), generator=g).double()
            ph = torch.rand(1, generator=g).item()*6.283
            v[...,c] += amp*torch.cos(sum(2*np.pi*k[i]*grid[i]/N for i in range(4))+ph)
    return qexp(v)

def apply_gauge(U, g):
    return torch.stack([qmul(qmul(g, U[m]), qinv(S(g, m))) for m in range(4)])

def perturb(U, eps, seed, smooth_amp=0.):
    g = torch.Generator().manual_seed(seed)
    n = eps*torch.randn(U.shape[:-1]+(3,), generator=g)
    out = qmul(qexp(n), U)
    return out

def plaq(U, m, n):
    a=U[m]; b=S(U[n],m); c=S(U[m],n); e=U[n]
    return a,b,c,e,qmul(qmul(qmul(a,b),qinv(c)),qinv(e))

def signs(U0):
    return {(m,n): plaq(U0,m,n)[4][...,0].sign() for m in range(4) for n in range(m+1,4)}

def defects(U, sg):
    ds=[]
    for (m,n),s in sg.items():
        P=plaq(U,m,n)[4]; c=P*s[...,None]; c=c-torch.tensor([1.,0,0,0]); ds.append(c.norm(dim=-1))
    return torch.stack(ds)

def hess_form(U, X, sg):
    """exact second derivative of the action at beta = 1"""
    tot=0.
    Q=imq(X)
    for (m,n),s in sg.items():
        a,b,c,e,P=plaq(U,m,n)
        abc=qmul(qmul(a,b),qinv(c))
        A=Q[m]; B=ad(a,S(Q[n],m)); C=-ad(abc,S(Q[m],n)); D=-ad(P,Q[n])
        ab=A+B; cd=C+D
        sc=qmul(A,A)+2*qmul(A,B)+qmul(B,B)+2*qmul(ab,cd)+qmul(C,C)+2*qmul(C,D)+qmul(D,D)
        cc=P*s[...,None]
        tot=tot-2*qmul(sc,cc)[...,0].sum()
    return tot

def T(U, m, f):  return ad(U[m], S(f, m))
def Tstar(U, m, f): return Sb(ad(qinv(U[m]), f), m)
def runavg(U, m, f, L):
    out=f; cur=f
    for j in range(1,L):
        cur=T(U,m,cur); out=out+cur
    return out/L
def block(U, f, L):
    for m in reversed(range(4)): f=runavg(U,m,f,L)
    return f
def form(U,X,sg,L,pen=0.25):
    Q=imq(X)
    dv=sum(Tstar(U,m,Q[m])-Q[m] for m in range(4))
    E=hess_form(U,X,sg)+(dv**2).sum()
    if L>0: E=E+pen/L**2*sum((block(U,Q[nu],L)**2).sum() for nu in range(4))
    return E

def lowest(U,sg,L,N,k=2):
    shape=(4,N,N,N,N,3); dim=int(np.prod(shape))
    def mv(v):
        x=torch.tensor(v).reshape(shape).requires_grad_(True)
        e=form(U,x,sg,L); g,=torch.autograd.grad(e,x)
        return (0.5*g).reshape(-1).numpy()
    op=LinearOperator((dim,dim),matvec=mv,dtype=np.float64)
    w=eigsh(op,k=k,which='SA',tol=1e-4,return_eigenvectors=False,maxiter=4000)
    return float(np.min(w))

def smooth_field(U0, amp, seed):
    N=U0.shape[1]; g=torch.Generator().manual_seed(seed)
    grid=torch.meshgrid(*[torch.arange(N,dtype=torch.float64)]*4,indexing='ij')
    A=torch.zeros(U0.shape[:-1]+(3,))
    for m in range(4):
        for c in range(3):
            k=torch.randint(-1,2,(4,),generator=g).double(); ph=torch.rand(1,generator=g).item()*6.283
            A[m,...,c]=amp*torch.cos(sum(2*np.pi*k[i]*grid[i]/N for i in range(4))+ph)
    return qmul(qexp(A),U0)

res=[]
for N,Ls in ((4,(0,1,2)),(6,(0,1,2,3)),(8,(0,1,2,4))):
    U0=flat(N); sg=signs(U0)
    bgs=[('flat',U0),('smooth.3',smooth_field(U0,0.3,5)),('smooth.8',smooth_field(U0,0.8,6)),('noise.02',perturb(U0,0.02,2))]
    for name,U in bgs:
        d=defects(U,sg); chord=(U-U0).norm(dim=-1).max().item()
        for L in Ls:
            lam=lowest(U,sg,L,N)
            r=dict(N=N,L=L,bg=name,sup_defect=d.max().item(),chord=chord,lam=lam,lamL2=lam*L**2 if L else None,lamN2=lam*N**2,proved_floor=(1/(16*L**2) if L else None))
            res.append(r); print(json.dumps(r),flush=True)
json.dump(res,open(sys.argv[1],'w'),indent=1)
