"""Do large-field plaquettes percolate? (numerics, not a proof).

Large-field plaquettes (a_p = 1 - z tr(P)/2 >= eps, eps ~ eps* = 0.27, the small-field threshold for side-2 block
convexity) have density ~ e^{-0.54 beta_std} and are present everywhere at the critical slope b*. A polymer (cluster)
expansion of large-field regions needs them to form finite clusters with an exponentially decaying size distribution:
a subcritical percolation condition, local and volume independent. Two plaquettes are connected when they share a link.
For each beta_std and n: density, mean cluster size excluding the largest (susceptibility), largest cluster fraction,
and the fraction of configurations with a cluster spanning the torus in some direction. The beta where spanning
probability falls with n locates the percolation threshold beta_perc: the beta_0 below which no polymer expansion of
eps*-large fields can converge.
Written before any run: at eps = 0.27, beta_perc is between 4 and 7 (density there 0.10-0.26; the plaquette-plaquette
graph has degree 24, so the site-percolation threshold is near 1/23 ~ 0.04-0.1).
Usage: out ns beta_stds n_cfg eps
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, scipy.sparse as sp
from scipy.sparse.csgraph import connected_components
from yang_mills_twisted_step_scaling import twist, heat, over, qmul, qc

def plaquettes(U,z):
    out=[]; planes=[]
    for m in range(4):
        for k in range(m+1,4):
            P=qmul(qmul(qmul(U[m],np.roll(U[k],-1,m)),qc(np.roll(U[m],-1,k))),qc(U[k]))
            out.append(1-(z if {m,k}=={1,2} else 1.)*P[...,0]); planes.append((m,k))
    return np.stack(out),planes                  # (6, N,N,N,N)

def incidence(N,planes):
    """Sparse (plaquette x link) incidence; plaquette index = plane*V + site, link index = dir*V + site."""
    V=N**4; x=np.indices((N,)*4).reshape(4,-1); site=lambda c: np.ravel_multi_index(c%N,(N,)*4)
    rows=[];cols=[]
    for pi,(m,k) in enumerate(planes):
        pid=pi*V+np.arange(V); em=np.zeros((4,1),int); em[m]=1; ek=np.zeros((4,1),int); ek[k]=1
        for d,c in ((m,x),(k,x+em),(m,x+ek),(k,x)):
            rows.append(pid); cols.append(d*V+site(c))
    return sp.csr_matrix((np.ones(4*6*V),(np.concatenate(rows),np.concatenate(cols))),shape=(6*V,4*V))

def clusters(a,inc,N,eps):
    big=np.flatnonzero(a.ravel()>=eps); nb=len(big)
    if nb==0: return dict(n=0,largest=0,chi=0.,span=False)
    B=inc[big]                                    # big plaquettes x links
    A=(B@B.T).tocsr()                             # share >= 1 link
    nc,lab=connected_components(A,directed=False)
    sizes=np.bincount(lab); imax=sizes.argmax()
    rest=np.delete(sizes,imax); chi=float((rest**2).sum()/nb) if len(rest) else 0.
    V=N**4; sites=big%V; coords=np.array(np.unravel_index(sites,(N,)*4))
    members=lab==imax; span=any(len(np.unique(coords[d][members]))==N for d in range(4))
    return dict(n=nb,largest=int(sizes[imax]),chi=chi,span=bool(span))

out=sys.argv[1]; ns=[int(x) for x in sys.argv[2].split(',')]; bs=[float(x) for x in sys.argv[3].split(',')]
ncfg=int(sys.argv[4]); eps=float(sys.argv[5]); res=[]
for N in ns:
    z=twist(N); par=np.indices((N,)*4).sum(0)%2; rng=np.random.default_rng(7+N)
    U=np.zeros((4,)+(N,)*4+(4,)); U[...,0]=1; xx=np.indices((N,)*4)
    U[1][xx[1]==0]=[0,1,0,0]; U[2][xx[2]==0]=[0,0,1,0]
    _,planes=plaquettes(U,z); inc=incidence(N,planes)
    for b in bs:
        for _ in range(150): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
        st=[]
        for c in range(ncfg):
            for _ in range(10): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
            a,_=plaquettes(U,z); st.append(clusters(a,inc,N,eps))
        P=6*N**4
        row=dict(N=N,bstd=b,eps=eps,cfgs=ncfg,density=float(np.mean([s['n'] for s in st])/P),
                 largest_frac=float(np.mean([s['largest']/max(s['n'],1) for s in st])),
                 largest_over_P=float(np.mean([s['largest'] for s in st])/P),
                 chi=float(np.mean([s['chi'] for s in st])),span_prob=float(np.mean([s['span'] for s in st])))
        res.append(row); print(json.dumps(row),flush=True); json.dump(res,open(out,'w'))
