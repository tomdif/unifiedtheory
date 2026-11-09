"""Twist free energy z(L) = Z_twisted / Z_periodic on L^4, SU(2) and the compact U(1) control (numerics, not a proof).

Thermodynamic integration with Gauss-Legendre nodes, errors from binning at each node, added in quadrature.
SU(2): coefficient lambda on the plaquettes of plane (1,2) at x1 = x2 = 0, lambda = 1 periodic, -1 twisted, so log z = -beta_std * int_{-1}^{1} sum_stack <tr U_p / 2> dlambda.
U(1): flux pi through the (1,2) plane spread evenly, phase c = lambda pi / L^2 on each (1,2) plaquette, log z = -beta (pi/L^2) int_0^1 sum_p <sin(P + c)> dlambda. Flux 2 pi is removable on the lattice, so pi is the analogue of the Z2 twist.
Written before any run. U(1): at beta = 1.5 and 1.1 (Coulomb) log z is flat in L, near -beta_R pi^2 / 2. At 0.9 (confined) log z rises to 0 with L. SU(2): log z rises to 0 with L, faster at smaller beta_std.
Kills z as a gap-sensitive observable: beta = 1.1 rising to 0 like beta = 0.9, the same blindness r showed. Passing shows only that it separates these phases. z bounds Wilson loops (Tomboulis-Yaffe), not the mass gap.
Usage: out.
"""
import os, sys, time, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0,os.path.dirname(__file__))
import numpy as np
from yang_mills_twisted_step_scaling import qmul,qc,S,heat,over
NODES=7; SECS={4:30,6:60,8:180}; X,W=np.polynomial.legendre.leggauss(NODES)

def su2(bstd,L,lam,secs,rng):
    z=np.ones((L,)*4); z[:,0,0,:]=lam; U=np.zeros((4,)+(L,)*4+(4,)); U[...,0]=1; par=np.indices((L,)*4).sum(0)%2; rec=[]
    for _ in range(150): heat(U,z,bstd/2,rng,par); over(U,z,par); over(U,z,par)
    tm=time.time()
    while time.time()-tm<secs:
        heat(U,z,bstd/2,rng,par); over(U,z,par); over(U,z,par)
        P=qmul(qmul(qmul(U[1],S(U[2],1)),qc(S(U[1],2))),qc(U[2]))
        rec.append(float(P[:,0,0,:,0].sum()))
    return np.array(rec)
def staple(T,m,c):
    st=0.
    for n in range(4):
        if n==m: continue
        f=np.exp(1j*c) if (m,n)==(1,2) else (np.exp(-1j*c) if (m,n)==(2,1) else 1.)
        st=st+f*np.exp(1j*(np.roll(T[n],-1,m)-np.roll(T[m],-1,n)-T[n]))
        st=st+np.conj(f)*np.roll(np.exp(1j*(-np.roll(T[n],-1,m)-T[m]+T[n])),1,n)
    return st
def u1(beta,L,lam,secs,rng):
    T=np.zeros((4,)+(L,)*4); par=np.indices((L,)*4).sum(0)%2; c=lam*np.pi/L**2; step=1.2/np.sqrt(max(1.,beta)); rec=[]
    def upd():
        for m in range(4):
            for p in (0,1):
                st=staple(T,m,c); d=rng.uniform(-step,step,T[m].shape)
                dS=beta*(np.real(np.exp(1j*(T[m]+d))*st)-np.real(np.exp(1j*T[m])*st))
                acc=(par==p)&(np.log(rng.random(T[m].shape))<dS); T[m][acc]=T[m][acc]+d[acc]
        for _ in range(3):
            for m in range(4):
                for p in (0,1):
                    a=np.angle(staple(T,m,c)); mask=par==p; T[m][mask]=(-2*a-T[m])[mask]
    for _ in range(150): upd()
    tm=time.time()
    while time.time()-tm<secs:
        upd()
        Pl=T[1]+np.roll(T[2],-1,1)-np.roll(T[1],-1,2)-T[2]
        rec.append(float(np.sin(Pl+c).sum()))
    return np.array(rec)
def err(a):
    b=np.array([x.mean() for x in np.array_split(a,10)]); return b.mean(),b.std(ddof=1)/np.sqrt(10)
out=sys.argv[1]; res=[]
Ls=[int(x) for x in sys.argv[2].split(',')] if len(sys.argv)>2 else [4,6,8]
scale=float(sys.argv[3]) if len(sys.argv)>3 else 1.
for group,b in (('u1',1.5),('u1',1.1),('u1',0.9),('su2',2.3),('su2',2.5)):
    for L in Ls:
        rng=np.random.default_rng(int(b*100)+L); tot=0.; var=0.; prof=[]
        for x,w in zip(X,W):
            if group=='su2':
                m,e=err(su2(b,L,float(x),SECS[L]*scale,rng)); g,gw=-b,w
            else:
                lam=(x+1)/2; m,e=err(u1(b,L,float(lam),SECS[L]*scale,rng)); g,gw=-b*np.pi/L**2,w/2
            tot+=g*gw*m; var+=(g*gw*e)**2; prof.append(float(m))
        r=dict(group=group,beta=b,L=L,log_z=float(tot),err=float(np.sqrt(var)),z=float(np.exp(tot)),profile=prof); res.append(r); print(json.dumps(r),flush=True); json.dump(res,open(out,'w'),indent=1)
