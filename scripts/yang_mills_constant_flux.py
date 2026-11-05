"""Constant-flux ('t Hooft) critical point on the twisted lattice (numerics, not a proof).

Abelian links U = exp(i sigma3 theta) with every twisted (1,2)-plaquette angle z P = exp(i sigma3 phi), phi = pi/n^2
(the twist supplies the missing pi). Its action is S = n^4 (1 - cos(pi/n^2)) -> pi^2/2 = 4.935, n-independent.
Abelian configurations with d*F = 0 are critical for the SU(2) action. Reports S, |grad S|, and the lowest Hessian
eigenvalues on the gauge-horizontal space (negative = unstable directions, zeros = abelian holonomy moduli).
Written before any run: |grad S| ~ 1e-15, S -> 4.93, and the Hessian has a negative eigenvalue (a saddle, the mountain
pass between center-related vacua), so the action gap eps0 in (ii') is at most pi^2/2.
Usage: out ns
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, torch, scipy.sparse.linalg as sla
from yang_mills_preconditioned_hessian import hessian, gauge_D
from yang_mills_twisted_step_scaling import twist
torch.set_default_dtype(torch.float64)
def tq(a,b):
    w1,x1,y1,z1=a.unbind(-1); w2,x2,y2,z2=b.unbind(-1)
    return torch.stack([w1*w2-x1*x2-y1*y2-z1*z2,w1*x2+x1*w2+y1*z2-z1*y2,w1*y2-x1*z2+y1*w2+z1*x2,w1*z2+x1*y2-y1*x2+z1*w2],-1)
CJ=torch.tensor([1.,-1,-1,-1])
def texp(a):
    th=torch.sqrt((a*a).sum(-1,keepdim=True)+1e-300)
    return torch.cat([torch.cos(th),torch.where(th>1e-8,torch.sin(th)/th,1-th*th/6)*a],-1)
def action(U,zt):
    tot=0.
    for m in range(4):
        for n in range(m+1,4):
            P=tq(tq(tq(U[m],torch.roll(U[n],-1,m)),torch.roll(U[m],-1,n)*CJ),U[n]*CJ)
            tot=tot+(1-(zt if {m,n}=={1,2} else 1.)*P[...,0]).sum()
    return tot


def flux_config(N):
    x=np.indices((N,)*4); xa=(x[1]-1)%N; xb=(x[2]-1)%N; phi=np.pi/N**2
    th=np.zeros((4,)+(N,)*4)
    th[2]=phi*xa
    th[1]=np.where(xa==N-1,-N*phi*xb,0.)
    U=np.zeros((4,)+(N,)*4+(4,)); U[...,0]=np.cos(th); U[...,3]=np.sin(th)
    return U

out=sys.argv[1]; ns=[int(v) for v in sys.argv[2].split(',')]; res=[]
for N in ns:
    z=twist(N); U=flux_config(N); zt=torch.tensor(z)
    eps=torch.zeros(4,N,N,N,N,3,requires_grad=True)
    S=action(tq(texp(eps),torch.tensor(U)),zt); g,=torch.autograd.grad(S,eps)
    # Hessian of S itself (bstd = 1). At a critical point H kills the gauge directions range(D) and preserves their
    # complement, so adding D D^T lifts the gauge zeros without moving the horizontal spectrum.
    D=gauge_D(U); H=(hessian(U,z,1.)+D@D.T).tocsc()
    vals=sla.eigsh(H,k=8,sigma=-1.,which='LM',return_eigenvectors=False)
    row=dict(N=N,S=float(S),S_formula=N**4*(1-np.cos(np.pi/N**2)),grad=float(g.norm()),lowest=sorted(map(float,vals)))
    res.append(row); print(json.dumps(row),flush=True); json.dump(res,open(out,'w'))
