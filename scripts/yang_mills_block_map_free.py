"""Exact weak-coupling limit of the block-map defects: beta * e_j in free field theory (numerics, not a proof).

Weight exp(-beta sum F_a^2) gives Feynman covariance 1/(2 beta khat^2) per colour, and e_j = 3 <F^(j)^2>. The linear
blocking kernel at level j+1 uses the spacing 2^j. Finite lattice sum over nonzero momenta, plaquettes averaged over
planes and sublattice offsets (translation invariance). Compares with the heatbath numbers via beta_eff = c_j / e_j.
"""
import os
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS'): os.environ[v]='2'
import sys, json, numpy as np

def kernel(k, a, alpha):
    """A'(k) = B(k) A(k) with B[...,m,n]; a = current spacing, new link from x to x+2a along m"""
    ph=np.exp(1j*k*a)                # shift by one current link
    B=np.zeros(k.shape[:-1]+(4,4),complex)
    for m in range(4):
        line=1+ph[...,m]
        B[...,m,m]+=line
        for n in range(4):
            if n==m: continue
            # up staple: A_n(x) + line A_m(x+n) - A_n(x+2m)
            B[...,m,m]+=alpha*ph[...,n]*line
            B[...,m,n]+=alpha*(1-ph[...,m]**2)
            # down staple: -A_n(x-n) + line A_m(x-n) + A_n(x-n+2m)
            pb=np.conj(ph[...,n])
            B[...,m,m]+=alpha*pb*line
            B[...,m,n]+=alpha*pb*(ph[...,m]**2-1)
    return B/(1+6*alpha)

def levels(N, alpha, jmax):
    g=2*np.pi*np.arange(N)/N
    k=np.stack(np.meshgrid(g,g,g,g,indexing='ij'),-1).reshape(-1,4)
    k=k[np.any(k!=0,axis=1)]
    khat2=(4*np.sin(k/2)**2).sum(-1)
    B=np.tile(np.eye(4,dtype=complex),(k.shape[0],1,1))
    out=[]
    for j in range(jmax+1):
        a=2**j
        D=np.exp(1j*k*a)-1     # forward difference at the current spacing
        tot=0.
        for m in range(4):
            for n in range(m+1,4):
                f=D[...,m,None]*B[:,n,:]-D[...,n,None]*B[:,m,:]
                tot=tot+(np.abs(f)**2).sum(-1)
        # 3 colours, covariance 1/(2 khat^2) at beta = 1, mean over momenta (N^4), mean over 6 planes
        out.append(float(3*(tot/6/(2*khat2)).sum()/N**4))
        B=kernel(k,a,alpha)@B
    return out

N=int(sys.argv[2]); res={}
for alpha in (0.,0.05,0.1,0.15,0.2,0.25,0.5,1.0):
    c=levels(N,alpha,int(sys.argv[3]))
    res[str(alpha)]=c
    print(alpha,'c_j=',[round(x,4) for x in c],'r=',[round(c[i+1]/c[i],3) for i in range(len(c)-1)],flush=True)
json.dump(res,open(sys.argv[1],'w'),indent=1)
