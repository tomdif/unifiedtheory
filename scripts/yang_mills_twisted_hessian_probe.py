# Exact lattice Hessian of the twisted SU(2) Wilson action at a flat twisted background.
# Second order: S_p = |sum_k Ad(prefix_k) X_k|^2 for z_p*P_p=1, so H = 2 C^T C.
import numpy as np, itertools, sys
from scipy.sparse import lil_matrix
from scipy.sparse.linalg import eigsh
def qm(a,b):
    return np.array([a[0]*b[0]-a[1]*b[1]-a[2]*b[2]-a[3]*b[3],a[0]*b[1]+a[1]*b[0]+a[2]*b[3]-a[3]*b[2],a[0]*b[2]-a[1]*b[3]+a[2]*b[0]+a[3]*b[1],a[0]*b[3]+a[1]*b[2]-a[2]*b[1]+a[3]*b[0]])
def qi(a): return np.array([a[0],-a[1],-a[2],-a[3]])
def Ad(p):
    R=np.zeros((3,3))
    for j in range(3):
        e=np.zeros(4);e[j+1]=1
        R[:,j]=qm(qm(p,e),qi(p))[1:]
    return R
one=np.array([1.,0,0,0]);I=np.array([0,1.,0,0]);J=np.array([0,0,1.,0]);Kq=np.array([0,0,0,1.])
def run(N,twist,dense=True):
    sites=list(itertools.product(range(N),repeat=4));sid={s:i for i,s in enumerate(sites)}
    lid=lambda s,m:(sid[s]*4+m)*3
    def U(s,m):
        if twist and m==1 and s[1]==0: return I
        if twist and m==2 and s[2]==0: return J
        return one
    st=lambda s,m:tuple((s[k]+(k==m))%N for k in range(4))
    planes=[(m,n) for m in range(4) for n in range(m+1,4)]
    C=lil_matrix((len(sites)*6*3,len(sites)*4*3));r=0;viol=0
    for s in sites:
        for m,n in planes:
            a,b,c,d=U(s,m),U(st(s,m),n),U(st(s,n),m),U(s,n)
            P=qm(qm(qm(a,b),qi(c)),qi(d))
            z=-1 if (twist and (m,n)==(1,2) and s[1]==0 and s[2]==0) else 1
            viol+=abs(z*P[0]-1)
            # U_k exp(X_k) forward; for inverse links: exp(-X)U^-1 
            p1=one; R1=Ad(p1)                # a exp(X1)
            R1=Ad(a)
            p2=qm(a,b); R2=Ad(p2)
            p3=p2; R3=-Ad(p3)                # (c exp X)^-1 = exp(-X)c^-1
            p4=qm(p2,qi(c)); R4=-Ad(p4)
            for R,l in ((R1,lid(s,m)),(R2,lid(st(s,m),n)),(R3,lid(st(s,n),m)),(R4,lid(s,n))):
                for i in range(3):
                    for j in range(3):
                        if abs(R[i,j])>1e-12: C[r+i,l+j]=C[r+i,l+j]+R[i,j]
            r+=3
    C=C.tocsr();H=(2*(C.T@C)).toarray()
    w=np.linalg.eigvalsh(H)
    null=int((w<1e-8).sum());nz=w[w>1e-8][:1][0]
    return viol,null,3*N**4,nz,w
for N in [3,4,5]:
    if N==5:
        pass
    for tw in (0,1):
        v,null,g,nz,w=run(N,tw)
        lab='n12=1' if tw else 'untwisted'
        pred=(2*4*np.sin(np.pi/(2*N))**2 if tw else 2*4*np.sin(np.pi/N)**2)
        print(f"N={N} {lab:10s} flat-violation={v:.1e} nullity={null} (3N^4={g}, physical zero modes={null-g}) lowest nonzero={nz:.6f} predicted k-min={pred:.6f}",flush=True)
