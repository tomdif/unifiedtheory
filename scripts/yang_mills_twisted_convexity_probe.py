#!/usr/bin/env python3
"""Smallest gauge-orthogonal eigenvalue of the second-order form of the twisted slice potential at
sampled fields. Second order, with Y_k the frame-transported link rotations and P0 the plaquette:
Q = z p0 |sum y|^2 - 2 z sum_{j<k} y_j^T [p]_x y_k. The flat value of the lowest mode is 4 sin^2(pi/2N).
Numerics on sampled fields only; not a proof of convexity."""
import numpy as np, sys, subprocess, itertools
def qm(a,b): return np.array([a[0]*b[0]-a[1]*b[1]-a[2]*b[2]-a[3]*b[3],a[0]*b[1]+a[1]*b[0]+a[2]*b[3]-a[3]*b[2],a[0]*b[2]-a[1]*b[3]+a[2]*b[0]+a[3]*b[1],a[0]*b[3]+a[1]*b[2]-a[2]*b[1]+a[3]*b[0]])
def qi(a): return np.array([a[0],-a[1],-a[2],-a[3]])
def Ad(p):
    a,b,c,d=p
    return np.array([[a*a+b*b-c*c-d*d,2*(b*c-a*d),2*(b*d+a*c)],[2*(b*c+a*d),a*a-b*b+c*c-d*d,2*(c*d-a*b)],[2*(b*d-a*c),2*(c*d+a*b),a*a-b*b-c*c+d*d]])
def cross(p): return np.array([[0,-p[2],p[1]],[p[2],0,-p[0]],[-p[1],p[0],0]])
def analyse(N,U):
    # U[x1,x2,x3,mu,4], mu=0,1,2 are lattice directions 1,2,3; c=x1+N*x2+N^2*x3
    idx=lambda x,m:(x[0]%N+N*(x[1]%N)+N*N*(x[2]%N))*3+m
    st=lambda x,m:tuple(x[i]+(i==m) for i in range(3))
    L=3*N**3; Q=np.zeros((3*L,3*L)); G=np.zeros((3*L,3*N**3)); val=lambda x,m:U[idx(x,m)]
    for x in itertools.product(range(N),repeat=3):
        for m,n in [(0,1),(0,2),(1,2)]:
            a,b,c,d=val(x,m),val(st(x,m),n),val(st(x,n),m),val(x,n)
            p2=qm(qm(a,b),qi(c)); P=qm(p2,qi(d))
            z=-1.0 if ((m,n)==(0,1) and x[0]==0 and x[1]==0) else 1.0
            Rs=[np.eye(3),Ad(a),-Ad(p2),-Ad(P)]
            ids=[idx(x,m),idx(st(x,m),n),idx(st(x,n),m),idx(x,n)]
            p0,pv=P[0],P[1:]; Cx=cross(pv)
            for j in range(4):
                for k in range(4):
                    blk=z*p0*Rs[j].T@Rs[k]
                    if j<k: blk=blk-z*Rs[j].T@Cx@Rs[k]
                    elif k<j: blk=blk-z*(Rs[k].T@Cx@Rs[j]).T
                    Q[3*ids[j]:3*ids[j]+3,3*ids[k]:3*ids[k]+3]+=blk
    sid=lambda x:(x[0]%N+N*(x[1]%N)+N*N*(x[2]%N))
    for x in itertools.product(range(N),repeat=3):
        for m in range(3):
            i=3*idx(x,m); G[i:i+3,3*sid(x):3*sid(x)+3]+=np.eye(3)
            y=st(x,m); G[i:i+3,3*sid(y):3*sid(y)+3]-=Ad(val(x,m))
    Q=(Q+Q.T)/2
    u,sv,_=np.linalg.svd(G,full_matrices=True); rank=(sv>1e-9).sum()
    Z=u[:,rank:]
    return np.linalg.eigvalsh(Z.T@Q@Z)[0]
if __name__=="__main__":
    bin_,N,conf=sys.argv[1],int(sys.argv[2]),int(sys.argv[3])
    tree=4*np.sin(np.pi/(2*N))**2
    print(f"N={N} tree lowest={tree:.4f}")
    for beta in sys.argv[4:]:
        out=subprocess.run([bin_,str(N),beta,"1","600",str(conf),"100","7",str(2*N)],capture_output=True,text=True).stdout
        D=np.fromstring(out,sep=" ").reshape(conf,-1,4)
        v=[analyse(N,D[i]) for i in range(conf)]
        print(f"  beta={beta:>7} lowest/tree mean={np.mean(v)/tree:+.3f} min={np.min(v)/tree:+.3f} max={np.max(v)/tree:+.3f}",flush=True)
