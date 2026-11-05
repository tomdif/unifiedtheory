"""Structure of the soft directions of the stochastic-localization posterior mu_t (numerics, not a proof).
Usage: python3 yang_mills_sl_softmode.py N beta_std t n_samples. Reports:
- the top-5 out-of-sample variances, with their gauge and radial fractions and participation;
- covariance on global left/right color-rotation spans;
- the Fourier content of the top directions;
- top variances local to side-2 blocks.
Companion to yang_mills_sl_covariance.py."""
import sys, json; sys.path.insert(0,__import__('os').path.dirname(__file__))
import numpy as np
src=open(__import__('os').path.join(__import__('os').path.dirname(__file__),'yang_mills_sl_covariance.py')).read().split("out=sys.argv[1];")[0]
exec(src)
N=int(sys.argv[1]); b=float(sys.argv[2]); t=float(sys.argv[3]); ns_=int(sys.argv[4])
z=twist(N); par=np.indices((N,)*4).sum(0)%2; rng=np.random.default_rng(5); beta=b/2
Us=np.zeros((4,)+(N,)*4+(4,)); Us[...,0]=1; xx=np.indices((N,)*4); Us[1][xx[1]==0]=[0,1,0,0]; Us[2][xx[2]==0]=[0,0,1,0]
for _ in range(200): heat(Us,z,beta,rng,par); over(Us,z,par); over(Us,z,par)
gauge_random(Us,rng)
y=t*Us+np.sqrt(t)*rng.normal(size=Us.shape)
def chain(seed):
    r=np.random.default_rng(seed); U=Us.copy(); X=[]
    for _ in range(30): heat_t(U,z,beta,y,r,par); over_t(U,z,beta,y,par); over_t(U,z,beta,y,par)
    for s_ in range(ns_):
        for _ in range(3): heat_t(U,z,beta,y,r,par); over_t(U,z,beta,y,par); over_t(U,z,beta,y,par)
        X.append(U.ravel().copy())
    return np.array(X)
XA=chain(1); XB=chain(2); A=XA-XA.mean(0); B=XB-XB.mean(0)
# top 5 directions of A by subspace iteration
V=np.random.default_rng(0).normal(size=(A.shape[1],5))
for _ in range(80):
    V=A.T@(A@V); V,_=np.linalg.qr(V)
mbar=XB.mean(0).reshape(Us.shape)
def gauge_basis(Uref):
    G=[]
    for x in np.ndindex(*(N,)*4):
        for a in range(1,4):
            ea=np.zeros(4); ea[a]=1.; d=np.zeros(Us.shape)
            for m in range(4):
                d[(m,)+x]+=qmul(ea,Uref[(m,)+x])                       # left action at x on links leaving x
                xm=list(x); xm[m]=(xm[m]-1)%N; xm=tuple(xm)
                d[(m,)+xm]-=qmul(Uref[(m,)+xm],ea)                     # right action on links entering x
            G.append(d.ravel())
    Q,_=np.linalg.qr(np.array(G).T); return Q
QG=gauge_basis(Us)
for i in range(5):
    v=V[:,i]; var_out=float(((B@v)**2).sum()/(len(B)-1)); gf=float(((QG.T@v)**2).sum())
    loc=np.linalg.norm(v.reshape(Us.shape),axis=-1)**2; pr=float(1/(loc**2).sum())
    # tangency to the link spheres at U*: radial component <v_l, U*_l>
    rad=float((np.einsum('...i,...i->...',v.reshape(Us.shape),Us)**2).sum())
    print(json.dumps(dict(i=i,var_out=round(var_out,3),gauge_frac_Ustar=round(gf,3),radial_frac_Ustar=round(rad,3),participation=round(pr,1),links=4*N**4)))
def structured(Uref,tag):
    W=[]
    for m in range(4):
        for a in range(4):
            ea=np.zeros(4); ea[a]=1.
            for side in ('L','R'):
                d=np.zeros(Us.shape); d[m]=qmul(ea,Uref[m]) if side=='L' else qmul(Uref[m],ea)
                W.append(d.ravel())
    W=np.array(W).T; Q,_=np.linalg.qr(W)
    C=(B@Q).T@(B@Q)/(len(B)-1); ev=np.linalg.eigvalsh(C)[::-1]
    # explained: how much of the top PCA direction lies in this span
    cap=[float(((Q.T@V[:,i])**2).sum()) for i in range(5)]
    print(json.dumps(dict(span=tag,dim=Q.shape[1],top_eigs=[round(float(e),3) for e in ev[:8]],top_pca_captured=[round(c,3) for c in cap])))
structured(Us,'Ustar')
structured(mbar/np.maximum(np.linalg.norm(mbar,axis=-1,keepdims=True),1e-9),'posterior_mean_dir')
# spatial spectrum of the top directions: fraction of |FFT|^2 at |k|^2 <= 1 (in units of (2pi/N)^2), and in U*-frame
for i in range(3):
    v=V[:,i].reshape(Us.shape)
    # express in U*-frame: v_l -> conj(U*_l) v_l (pure rotation per link, isometric)
    vf=np.stack([qmul(qc(Us[m]),v[m]) for m in range(4)])
    out={}
    for name,arr in (('raw',v),('Uframe',vf)):
        F=np.abs(np.fft.fftn(arr,axes=(1,2,3,4)))**2; F=F.sum(axis=(0,5))
        k=np.fft.fftfreq(N)*N; K2=sum(np.meshgrid(*[k**2]*4,indexing='ij'))
        out[name]=dict(k0=round(float(F[K2==0].sum()/F.sum()),3),k_le1=round(float(F[K2<=1].sum()/F.sum()),3),k_le2=round(float(F[K2<=2].sum()/F.sum()),3))
    print(json.dumps(dict(i=i,**out)))
# local clusters: per side-2 block (links based in the block), top direction from chain A, variance on chain B
XA4=A.reshape((len(A),)+Us.shape); XB4=B.reshape((len(B),)+Us.shape); loc=[]
for b0 in np.ndindex(*(N//2,)*4):
    sl=tuple(slice(2*c,2*c+2) for c in b0)
    a=XA4[(slice(None),slice(None))+sl].reshape(len(A),-1); bb=XB4[(slice(None),slice(None))+sl].reshape(len(B),-1)
    w,E=np.linalg.eigh(a.T@a/(len(a)-1)); v=E[:,-1]
    loc.append(float(((bb@v)**2).sum()/(len(bb)-1)))
loc=np.array(loc)
print(json.dumps(dict(local_block_top=dict(max=round(float(loc.max()),3),median=round(float(np.median(loc)),3),min=round(float(loc.min()),3),blocks=len(loc)))))
