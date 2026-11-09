"""Spectral gap of the von Mises–Fisher law exp(kappa <e,U>) on S^3 (numerics). Calibration: kappa = 0 gives 3 = lambda_1(S^3)."""
# spectral gap of vMF_kappa on S^3 (Laplace-Beltrami Dirichlet form), via sectors l of S^2-fiber harmonics:
# -(w f')'/w + l(l+1)/sin^2 th f, w = sin^2 th e^{kappa cos th}, th in (0,pi). Finite elements (generalized eig).
import numpy as np, scipy.linalg as sl
def gap(k,M=3000):
    th=np.linspace(0,np.pi,M+1); h=th[1]-th[0]; mid=(th[:-1]+th[1:])/2
    wm=np.sin(mid)**2*np.exp(k*(np.cos(mid)-1))
    best=[]
    for l in range(0,4):
        # nodes 0..M; for l>=1 Dirichlet at both ends; for l=0 free
        A=np.zeros((M+1,M+1)); B=np.zeros((M+1,M+1))
        for i in range(M):
            ke=wm[i]/h*np.array([[1,-1],[-1,1]])
            me=wm[i]*h/6*np.array([[2,1],[1,2]])
            pe=l*(l+1)*np.exp(k*(np.cos(mid[i])-1))*h/6*np.array([[2,1],[1,2]])   # w/sin^2 = e^{..}
            A[i:i+2,i:i+2]+=ke+pe; B[i:i+2,i:i+2]+=me
        if l>=1: A=A[1:-1,1:-1]; B=B[1:-1,1:-1]
        ev=sl.eigh(A,B,eigvals_only=True,subset_by_index=[0,2])
        best.append(ev[1] if l==0 else ev[0])
    return best
for k in (3,4,6,8,200,500):
    g=gap(k,1500); print(k,[round(x,3) for x in g],'gap',round(min(g),3),'gap/max(k,1)',round(min(g)/max(k,1),3))
