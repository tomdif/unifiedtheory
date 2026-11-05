"""Rigorous two-sided bound on the SU(2) plaquette from loop equations and positivity alone (numerics, not a proof).

Infinite volume, no sampling. W(C) = <tr U_C / 2>. For M = U A with U a link of C, integration by parts gives, with Fierz for SU(2):
  0 = -(3/4) tr M + sum over further occurrences of U in A = B U C: -(1/4) tr M - (1/2) tr(B C^-1),  of U^-1 in A = B U^-1 C: (1/4) tr M + (1/2) tr(U B U^-1 C^-1)
      - (beta/8) sum_staples s [ tr(U A U s) - tr(A s^-1) ],    S = beta sum_p (1 - tr U_p / 2),
so the equations are linear in single traces. Positivity: for paths P_i with one endpoint, the matrix tr(P_i^-1 P_j) / 2 is positive semidefinite.
Equations use loops up to length Lmax - 4, positivity uses paths up to length ell. Loops are identified under cyclic rotation, inversion and the lattice symmetry group.
Stated before the run. Checks: every equation holds on Monte Carlo within errors (mc mode); D = 2 bounds contain I2/I1(beta). Use: at D = 4, beta = 2.3 the bounds must contain about 0.602 (recalled).
Worth pursuing as a route to a certificate if the width at Lmax = 12 is below 0.05. A wider result does not rule it out, since published runs reach length 24, but it means a small setup will not do.
Modes: mc beta N sweeps; bound D beta Lmax ell.
"""
import os, sys, json, time
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0,os.path.dirname(__file__))
import numpy as np

def reduce(w):
    out=[]
    for x in w:
        if out and out[-1]==-x: out.pop()
        else: out.append(x)
    i,j=0,len(out)
    while j-i>=2 and out[i]==-out[j-1]: i+=1; j-=1
    return tuple(out[i:j])
def inv(w): return tuple(-x for x in reversed(w))
def relabel(w):
    m={}; out=[]
    for x in w:
        a=abs(x)
        if a not in m: m[a]=(len(m)+1)*(1 if x>0 else -1)
        l=m[a]; out.append(l if x>0 else -l)
    return tuple(out)
memo={}
def canon(w):
    w=reduce(w)
    if w in memo: return memo[w]
    best=None
    for v in (w,inv(w)):
        for k in range(len(v)):
            r=relabel(v[k:]+v[:k])
            if best is None or r<best: best=r
    if best is None: best=()
    memo[w]=best
    return best
def staples(mu,D):
    a=abs(mu); s=1 if mu>0 else -1; out=[]
    for n in range(1,D+1):
        if n==a: continue
        for e in (n,-n): out.append((e,-mu,-e))
    return out
def equation(word,beta,D):
    """{canonical loop: coefficient}, for the first link of word; sum over loops of coefficient * tr = 0, with tr = 2 W."""
    eq={}
    def add(w,c):
        k=canon(w); eq[k]=eq.get(k,0.)+c
    U=word[0]; A=word[1:]; add(word,-0.75)
    def link(p,x):
        # the physical link under step x from site p, with its orientation
        if x>0: return (p,x),1
        q=list(p); q[-x-1]-=1
        return (tuple(q),-x),-1
    def step(p,x):
        q=list(p); q[abs(x)-1]+=1 if x>0 else -1
        return tuple(q)
    p0=(0,)*D; l0,o0=link(p0,U); p=step(p0,U)
    for i,x in enumerate(A):
        B,C=A[:i],A[i+1:]; l,o=link(p,x)
        if l==l0 and o==o0:
            add(word,-0.25); add(B+inv(C),-0.5)
        elif l==l0:
            add(word,0.25); add((U,)+B+(-U,)+inv(C),0.5)
        p=step(p,x)
    for s in staples(U,D):
        add((U,)+A+(U,)+s,-beta/8); add(A+inv(s),beta/8)
    return eq
def closed_words(D,L):
    letters=[x for d in range(1,D+1) for x in (d,-d)]; seen=set()
    def rec(w,pos):
        n=len(w)
        if n and not any(pos): 
            r=reduce(w)
            if len(r)==n: seen.add(canon(w))
        if n==L: return
        for x in letters:
            if n and w[-1]==-x: continue
            if sum(map(abs,pos))-1>L-n-1 and False: continue
            p=list(pos); p[abs(x)-1]+=1 if x>0 else -1
            if sum(map(abs,p))>L-n-1: continue
            rec(w+(x,),p)
    rec((),[0]*D)
    seen.discard(())
    return sorted(seen,key=lambda w:(len(w),w))

def tr_field(U,w):
    from yang_mills_twisted_step_scaling import qmul,qc
    P=None; shift=[0,0,0,0]
    for x in w:
        a=abs(x)-1
        if x>0:
            f=np.roll(U[a],[-s for s in shift],axis=(0,1,2,3)); shift[a]+=1
        else:
            shift[a]-=1; f=qc(np.roll(U[a],[-s for s in shift],axis=(0,1,2,3)))
        P=f if P is None else qmul(P,f)
    return 2*P[...,0].mean()
def mc(beta,N,sweeps):
    from yang_mills_twisted_step_scaling import heat,over
    rng=np.random.default_rng(1); U=np.zeros((4,N,N,N,N,4)); U[...,0]=1; z=np.ones((N,)*4); par=np.indices((N,)*4).sum(0)%2
    eqs=[]
    for w in closed_words(4,8):
        for k in {0,1,2}:
            r=w[k:]+w[:k]
            eqs.append((r,equation(r,beta,4)))
    names=sorted({k for _,e in eqs for k in e if k})
    tr={k:[] for k in names}
    for _ in range(100): heat(U,z,beta/2,rng,par); over(U,z,par)
    for _ in range(sweeps):
        heat(U,z,beta/2,rng,par); over(U,z,par)
        for k in names: tr[k].append(tr_field(U,k))
    worst=[]
    for r,e in eqs:
        v=np.zeros(sweeps)
        for k,c in e.items(): v=v+c*(np.array(tr[k]) if k else 2.)
        b=np.array([x.mean() for x in np.array_split(v,20)])
        worst.append((abs(b.mean())/(b.std(ddof=1)/np.sqrt(20)),b.mean(),len(r),r))
    worst.sort(key=lambda t:-t[0])
    print(json.dumps(dict(n_eq=len(eqs),n_loops=len(names),plaq=float(np.mean(tr[(1,2,-1,-2)])/2),worst=[(float(a),float(b),c,list(d)) for a,b,c,d in worst[:5]],frac_z_over_3=float(np.mean([t[0]>3 for t in worst])))))
def paths(D,ell):
    letters=[x for d in range(1,D+1) for x in (d,-d)]; out={}
    def rec(w,pos):
        out.setdefault(tuple(pos),set()).add(w)
        if len(w)==ell: return
        for x in letters:
            if w and w[-1]==-x: continue
            p=list(pos); p[abs(x)-1]+=1 if x>0 else -1
            rec(w+(x,),p)
    rec((),[0]*D)
    return out
def bound(D,beta,Lmax,ell):
    import cvxpy as cp, scipy.sparse as sp
    t0=time.time(); seeds=closed_words(D,Lmax-4); idx={}
    def var(k): return idx.setdefault(k,len(idx))
    rows=[]
    for w in seeds:
        for j in range(len(w)):
            r=w[j:]+w[:j]; rows.append(equation(r,beta,D))
    uniq={}
    for e in rows:
        c=tuple(sorted((k,round(v,12)) for k,v in e.items() if abs(v)>1e-13))
        uniq[c]=e
    rows=list(uniq.values())
    for e in rows:
        for k in e:
            if k: var(k)
    blocks=[]
    P=paths(D,ell)
    for end,ws in P.items():
        if list(end)!=sorted(end,reverse=True) or min(end)<0: continue
        ws=sorted(ws,key=lambda w:(len(w),w))
        if len(ws)<2: continue
        ent={}
        for i,a in enumerate(ws):
            for j,b in enumerate(ws[i:],i):
                ent[(i,j)]=canon(inv(a)+b)
                if ent[(i,j)]: var(ent[(i,j)])
        blocks.append((len(ws),ent))
    plaq=var(canon((1,2,-1,-2)))
    n=len(idx); x=cp.Variable(n)
    I=[];J=[];V=[];b=[]
    for i,e in enumerate(rows):
        c0=0.
        for k,v in e.items():
            if k: I.append(i);J.append(idx[k]);V.append(2*v)
            else: c0+=2*v
        b.append(-c0)
    A=sp.csr_matrix((V,(I,J)),shape=(len(rows),n)); cons=[A@x==np.array(b),x<=1,x>=-1]
    for m,ent in blocks:
        ri=[];rj=[];rv=[];c=np.zeros(m*m)
        for (i,j),k in ent.items():
            for a in [i*m+j]+([j*m+i] if i!=j else []):
                if k: ri.append(a);rj.append(idx[k]);rv.append(1.)
                else: c[a]=1.
        B=sp.csr_matrix((rv,(ri,rj)),shape=(m*m,n))
        M=cp.reshape(B@x+c,(m,m),order='C'); cons.append(M>>0)
    out={}
    for name,obj in (('lower',cp.Minimize(x[plaq])),('upper',cp.Maximize(x[plaq]))):
        pr=cp.Problem(obj,cons); pr.solve(solver=cp.CLARABEL); out[name]=float(x[plaq].value) if x.value is not None else None; out[name+'_status']=pr.status
    r=dict(D=D,beta=beta,Lmax=Lmax,ell=ell,n_vars=n,n_eq=len(rows),blocks=[m for m,_ in blocks],secs=time.time()-t0,**out)
    print(json.dumps(r),flush=True); return r
if __name__=='__main__':
    if sys.argv[1]=='mc': mc(float(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]))
    else: bound(int(sys.argv[2]),float(sys.argv[3]),int(sys.argv[4]),int(sys.argv[5]))
