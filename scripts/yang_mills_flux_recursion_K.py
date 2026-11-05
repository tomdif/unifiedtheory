"""The constant in the flux-sector doubling inequality on SU(2), lattices L^4, (L,2L,L,L), (L,2L,2L,L) (numerics, not a proof).

y = (1-z)/(1+z), Z_0 = Z (1+z)/2. Exact for T >= 0: y(S1) <= K1 y(S0)^2 and y(S2) <= K2 y(S1)^2, with K1 = Z_0(S0)^2/Z_0(S1), K2 = Z_0(S1)^2/Z_0(S2), K3 = K1^2 K2.
log Z differences come from integrating the plaquette in beta_std from 1.4, with the sum over all six planes. Below 1.4 the finite-size difference is taken as 0, an assumption.
z comes from integration in lambda on the (1,2) stack as in yang_mills_twist_free_energy.py, 7 nodes.
Written before any run:
  Bug check: both one-step inequalities hold within errors. A violation above 2 sigma means a bug or a wrong derivation.
  Prediction: y(S0) < K3^(-1/3), so the recursion contracts from L = 4, at beta_std = 2.2 and 2.3. It does not at 2.5.
  Decisive: K3 at L = 4 versus L = 6 at fixed beta_std. Uniform control needs log K3 not growing with L. If it grows like the volume, the recursion is empty.
L = 6 run, chosen after reading the L = 4 plaquette integrand and before any K was computed: that integrand is consistent with 0 below beta_std = 2.1 at L = 4, so L = 6 starts the integral at 2.2, an assumption tested by the integrand at 2.2. Stated for L = 6: log K3 within 1.5 of its L = 4 value or smaller keeps the recursion alive. Above 5 times it (the volume ratio) empties it.
Usage: out L betas secs_plaq secs_z [grid_start].
"""
import os, sys, time, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0,os.path.dirname(__file__))
import numpy as np
from yang_mills_twisted_step_scaling import qmul,qc,S,heat,over
X,W=np.polynomial.legendre.leggauss(7); G0=float(sys.argv[6]) if len(sys.argv)>6 else 1.4; GRID=np.arange(G0,2.5001,0.1)

def setup(shape,lam):
    z=np.ones(shape); z[:,0,0,:]=lam; U=np.zeros((4,)+shape+(4,)); U[...,0]=1
    return z,U,np.indices(shape).sum(0)%2
def run(shape,bstd,lam,secs,rng,obs):
    z,U,par=setup(shape,lam); rec=[]
    def upd(): heat(U,z,bstd/2,rng,par); over(U,z,par); over(U,z,par)
    for _ in range(150): upd()
    tm=time.time()
    while time.time()-tm<secs: upd(); rec.append(obs(U))
    b=np.array([x.mean() for x in np.array_split(np.array(rec),10)])
    return b.mean(),b.std(ddof=1)/np.sqrt(10)
def plaq_sum(U):
    t=0.
    for m in range(4):
        for n in range(m+1,4): t+=qmul(qmul(qmul(U[m],S(U[n],m)),qc(S(U[m],n))),qc(U[n]))[...,0].sum()
    return float(t)
def stack(U):
    return float(qmul(qmul(qmul(U[1],S(U[2],1)),qc(S(U[1],2))),qc(U[2]))[:,0,0,:,0].sum())

out,L=sys.argv[1],int(sys.argv[2]); betas=[float(b) for b in sys.argv[3].split(',')]; sp,sz=float(sys.argv[4]),float(sys.argv[5])
shapes=[(L,L,L,L),(L,2*L,L,L),(L,2*L,2*L,L)]; rng=np.random.default_rng(1000+L); res=dict(L=L,grid=GRID.tolist(),plaq=[],z=[],out=[])
for g in GRID:
    row=[run(s,float(g),1.,sp,rng,plaq_sum) for s in shapes]; res['plaq'].append(row); print('plaq',round(float(g),2),row,flush=True); json.dump(res,open(out,'w'))
P=np.array(res['plaq'])
def diff(i,bmax):
    # integral from G0 to bmax of 2 P_i - P_{i+1}, trapezoid on the grid; the errors add in quadrature
    k=int(round((bmax-G0)/0.1))+1; w=np.full(k,0.1); w[0]=w[-1]=0.05
    v=2*P[:k,i,0]-P[:k,i+1,0]; e=np.sqrt(4*P[:k,i,1]**2+P[:k,i+1,1]**2)
    return float((w*v).sum()),float(np.sqrt(((w*e)**2).sum()))
for b in betas:
    zs=[]
    for s in shapes:
        tot=0.; var=0.
        for x,w in zip(X,W):
            m,e=run(s,b,float(x),sz,rng,stack); tot+=-b*w*m; var+=(b*w*e)**2
        zs.append((tot,float(np.sqrt(var))))
    res['z'].append(dict(beta=b,logz=zs))
    lz=np.array([a for a,_ in zs]); z=np.minimum(np.exp(lz),1.); y=(1-z)/(1+z); l0=np.log((1+z)/2)
    d1,e1=diff(0,b); d2,e2=diff(1,b)
    lK1=d1+2*l0[0]-l0[1]; lK2=d2+2*l0[1]-l0[2]; lK3=2*lK1+lK2
    r=dict(beta=b,L=L,y=y.tolist(),logz=zs,logK1=[lK1,e1],logK2=[lK2,e2],logK3=[lK3,float(np.sqrt(4*e1**2+e2**2))],ystar=float(np.exp(-lK3/3)),
           step1=[float(y[1]),float(np.exp(lK1)*y[0]**2)],step2=[float(y[2]),float(np.exp(lK2)*y[1]**2)])
    res['out'].append(r); print(json.dumps(r),flush=True); json.dump(res,open(out,'w'))
